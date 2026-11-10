-- Prove2me | Theorems.Thm_GoodHypotheses_Proper_theorem_1_1
-- name    : GoodHypotheses.Proper.theorem_1_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T00:15:22.493185+00:00
-- url     : https://prove2.me/theorems/57abcf4c-fcf3-4b92-ae9e-ba0ac7c821be
-- title:
--   Theorem 1.1 — proper hypothesis selection: 3OPT + ε with O(ε⁻² log(n/δ)) samples and O(nε⁻² log(n/δ)) time, with probability 1 − δ
-- statement:
--   Let $(X,\mu)$ be any measure space, $h_1,\dots,h_n$ ($n\ge1$) known hypotheses and $p$ an unknown target, all probability densities with respect to $\mu$; the algorithm can draw samples from $p$ and from every $h_i$ and evaluate $h_i(x)$, each in constant time, but has no density access to $p$. Let $\mathrm{OPT}=\min_id_{TV}(p,h_i)$. There is an algorithm that takes $s=O(\varepsilon^{-2}\log(n/\delta))$ samples from $p$, runs in $O(n\varepsilon^{-2}\log(n/\delta))$ time and outputs $h_{out}\in\{h_1,\dots,h_n\}$ such that, with probability at least $1-\delta$,
--   $$d_{TV}(h_{out},p)\le3\,\mathrm{OPT}+\varepsilon .$$
--   Formally: there are a universal constant $C>0$ and one admissible program of the randomized oracle real RAM such that for every measurable space $X$ with any measure $\mu$, every $n\ge1$, all probability densities $h_1,\dots,h_n,p$, every $\varepsilon>0$ and $\delta\in(0,1)$, on input $(n,\varepsilon,\delta)$ every run halts within $C\,n\,\varepsilon^{-2}\log(n/\delta)+C$ steps, draws at most $C\,\varepsilon^{-2}\log(n/\delta)+C$ samples from $p$ and outputs an index in $[n]$, and the probability over the tape that $d_{TV}(h_{out},p)\le3\,\mathrm{OPT}+\varepsilon$ fails is at most $\delta$.
--
--   The factor 3 is optimal for proper selection, and the sample complexity is optimal; the result removes the $\mathrm{poly}(1/\delta)$ running time of earlier near-linear algorithms.
--
--   Differences from the source:
--
--   - reading: "runs in time", constant-time sampling and density queries (pp. 1–2, §3) → the number of executed instructions of an Admissible program of the unit-cost randomized real RAM `Machine` (SmaleNinth core, integer memory, exp, log, uniform tape, opaque X-registers with sampleP, sampleH, evalH, halt; rational literals, no floor); reason: the paper names no machine; every arithmetic operation and every oracle call costs one unit
--   - encoding: O(ε⁻² log(n/δ)) samples, O(nε⁻² log(n/δ)) time → C·log(n/δ)/ε² + C samples and C·n·log(n/δ)/ε² + C steps, one universal C fixed before X, μ, n, the densities, ε and δ, together with the program; reason: explicit constant; the additive C covers parameters where the expression is below 1
--   - encoding: the algorithm's sample count and running time → bounds on every run, i.e. for every tape (worst case), not in expectation; reason: the paper's bounds are deterministic (T rounds of O(n) work)
--   - encoding: with probability at least 1 − δ → tapeLaw(failure set) ≤ δ, the failure set being {ω | no output index i with d_TV(h_i, p) ≤ 3·OPT + ε}; reason: a lower bound on a possibly non-measurable success set would be read as an outer measure, which is weaker
--   - encoding: randomness: fresh samples from p and the h_i, and the algorithm's coins → a product tape (i.i.d. samples of p, i.i.d. samples of each h_i, i.i.d. Uniform[0,1]) under tapeLaw, read sequentially; reason: every cell is read at most once, so it has the law of fresh adaptive draws
--   - encoding: probability densities h_i, p w.r.t. µ, sampled from → IsDensityOf μ (Ph i) (h i), IsDensityOf μ Pp p: measurable, nonnegative, with laws Ph i = h_i·μ, Pp = p·μ; reason: a probability density is exactly the density of a probability law
--   - encoding: input (ε, δ, n) and output h_out ∈ H → n in integer memory cell 0, ε and δ in real memory cells 0, 1; the output is the 0-based index in pointer register 0 at halting, required to lie in [0, n) on every run; reason: input/output layout; Fin n
-- source:
--   Aamand, Aliakbarpour, Chen, Silwal, Stevens, Zou, A Good Way to Find Good Hypotheses, STOC 2027 submission (manuscript sha256 a428fbe0…), p. 3, Theorem 1.1 (restated and proved pp. 22–23)

import Mathlib
import Definitions.Def_GoodHypotheses_Proper_Densities
import Definitions.Def_GoodHypotheses_Proper_Machine

open MeasureTheory

namespace GoodHypotheses.Proper

/-- Theorem 1.1 (Proper Guarantee, p. 3): there are a universal constant `C` and one fixed
admissible program of the randomized oracle real RAM such that for every measurable space `X`
with any measure `μ`, every `n ≥ 1`, all probability densities `h_1, …, h_n, p` with respect to
`μ` (of the laws `Ph i`, `Pp`), every `ε > 0` and `δ ∈ (0, 1)`, on input `(n, ε, δ)`: every run
(every tape) halts within `C n ε⁻² log(n/δ) + C` steps, draws at most `C ε⁻² log(n/δ) + C`
samples from `p` and outputs an index `i_out ∈ [n]`; and the probability, over the independent
samples and uniform draws, that `dTV(h_{i_out}, p) ≤ 3 OPT + ε` fails is at most `δ`. -/
theorem theorem_1_1 :
    ∃ C : ℝ, 0 < C ∧ ∃ P : Program, Admissible P ∧
      ∀ (X : Type) [MeasurableSpace X] (μ : Measure X) (n : ℕ) (h : Fin n → X → ℝ) (p : X → ℝ)
        (Ph : Fin n → ProbabilityMeasure X) (Pp : ProbabilityMeasure X) (ε δ : ℝ),
        1 ≤ n → (∀ i, IsDensityOf μ (Ph i) (h i)) → IsDensityOf μ Pp p →
        0 < ε → 0 < δ → δ < 1 →
        (∀ ω : Tape X n,
            HaltsWithin P h ω (selectionInput X n ε δ)
                (C * n * Real.log (n / δ) / ε ^ 2 + C) ∧
              SamplesWithin P h ω (selectionInput X n ε δ)
                (C * Real.log (n / δ) / ε ^ 2 + C) ∧
              (outIndex P h ω (selectionInput X n ε δ)).isSome) ∧
          tapeLaw Pp Ph {ω | ¬ ∃ i, outIndex P h ω (selectionInput X n ε δ) = some i ∧
              tvDist μ (h i) p ≤ 3 * OPT μ p h + ε}
            ≤ ENNReal.ofReal δ := by sorry

end GoodHypotheses.Proper
