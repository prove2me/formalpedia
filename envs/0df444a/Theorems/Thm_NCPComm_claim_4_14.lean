-- Prove2me | Theorems.Thm_NCPComm_claim_4_14
-- name    : NCPComm.claim_4_14
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:04:17.070526+00:00
-- url     : https://prove2.me/theorems/fadcb616-6bc2-4d3c-a9c6-d3eca15c230b
-- title:
--   Claim 4.14 — abort probability
-- statement:
--   For the parameters of Proposition 4.7, let
--   $$
--   \mu_h:=\frac{s^2}{16K}e^{-s/(4K)},\qquad|a|=\Big\lfloor\frac{\mu_h}4\Big\rfloor.
--   $$
--   The setup of Figure 4.9.1 satisfies, uniformly over the promised inputs $a,b$,
--   $$
--   \Pr[\mathrm{abort}]\le e^{-9\mu_h/32}+\frac{s}{2K}+\frac{s}{2(N-K)}+\frac{s^3}{192(N-K)^2}=o(1).
--   $$
--   Moreover, $|a|=\Theta(s^2/K)$.
--
--   This is what makes the setup usable in a protocol: aborts cost only $o(1)$ in distance.
--
--   Differences from the source:
--   - encoding: asymptotic statement in N with o(·), O(·), Ω(·) → sequences N(n), K(n), s(n) with limits and "for all large n"; reason: decision 11 of the plan; a family of parameters is what the asymptotic notation quantifies over
--   - generalization: the displayed inequality under the parameters of Proposition 4.7, on promised inputs → the inequality at every valid (N, K, s), for every a with |a| = ⌊μ_h/4⌋ and every b; reason: its proof is nonasymptotic and reads a only through |a| and b not at all; the regime and the promise are special cases
--   - generalization: "o(1)" and Θ for a sufficiently large C₁ → both for every C₁ > 0; reason: the proof uses s = Ω(√N) only through μ_h → ∞; large C₁ is a special case
--   - reading: |a| = Θ(s²/K) with constants unnamed on the page → ∃ c, C absolute, quantified before C₁ and the sequences, with the bounds for all large n; reason: the stronger reading; |a| ≤ s²/(64K) always, and |a| ≥ s²/(256K) once e^{−s/(4K)} ≥ 1/2 and μ_h/4 ≥ 1
-- source:
--   Herman, The Communication Complexity of Verifying Distribution Properties, STOC 2027 submission (manuscript sha256 714c0353…), Claim 4.14, p.29

import Mathlib
import Definitions.Def_NCPComm_setupProcedure

open scoped NNReal ENNReal Topology
open Filter

namespace NCPComm

/-- **Claim 4.14 (Abort probability), p.29** (Herman, The Communication Complexity of Verifying
Distribution Properties, STOC 2027 submission, manuscript sha256 714c0353…). With
`μ_h := (s²/(16K)) e^{-s/(4K)}` and `|a| = ⌊μ_h/4⌋`, the setup of Figure 4.9.1 satisfies, uniformly
over the inputs,
`Pr[abort] ≤ e^{-9μ_h/32} + s/(2K) + s/(2(N-K)) + s³/(192(N-K)²)`, and in the parameters of
Proposition 4.7 this bound is `o(1)` and `|a| = Θ(s²/K)`.

**Formalization Note** The explicit inequality holds at every valid parameter and every `a` with
`|a| = ⌊μ_h/4⌋` and every `b`, which is more general than the promise of the page. The asymptotic part
holds for every positive `C₁`, so `C₁` is quantified universally. The constants `c, C` of
`|a| = Θ(s²/K)` are absolute, quantified before `C₁` and the sequences; only the threshold in `n`
depends on the sequence. `⌊μ_h/4⌋` is `inputSizeA K s`. -/
theorem claim_4_14 :
    (∀ (N K : ℕ) (s : ℝ≥0) (a b : Fin N → Bool), ValidParams N K →
      let μh : ℝ := (s : ℝ) ^ 2 / (16 * K) * Real.exp (-(s : ℝ) / (4 * K))
      weight a = ⌊μh / 4⌋₊ →
      setupProcedure N K s a b none ≤ ENNReal.ofReal
        (Real.exp (-(9 * μh / 32)) + (s : ℝ) / (2 * K) + (s : ℝ) / (2 * ((N : ℝ) - K))
          + (s : ℝ) ^ 3 / (192 * ((N : ℝ) - K) ^ 2))) ∧
    (∀ C₁ : ℝ, 0 < C₁ → ∀ (K : ℕ → ℕ) (s : ℕ → ℝ≥0), InRegime C₁ K s →
      Tendsto (fun n =>
          let μh : ℝ := (s n : ℝ) ^ 2 / (16 * K n) * Real.exp (-(s n : ℝ) / (4 * K n))
          Real.exp (-(9 * μh / 32)) + (s n : ℝ) / (2 * K n) + (s n : ℝ) / (2 * ((3 * n : ℝ) - K n))
            + (s n : ℝ) ^ 3 / (192 * ((3 * n : ℝ) - K n) ^ 2)) atTop (𝓝 0)) ∧
    (∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ C₁ : ℝ, 0 < C₁ → ∀ (K : ℕ → ℕ) (s : ℕ → ℝ≥0),
      InRegime C₁ K s → ∀ᶠ n in atTop,
        c * ((s n : ℝ) ^ 2 / K n) ≤ (inputSizeA (K n) (s n) : ℝ) ∧
        (inputSizeA (K n) (s n) : ℝ) ≤ C * ((s n : ℝ) ^ 2 / K n)) := by sorry

end NCPComm
