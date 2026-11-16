-- Prove2me | Theorems.Thm_LeakageSpectral_Shannon_Supplement_theorem_5
-- name    : LeakageSpectral.Shannon.Supplement.theorem_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T17:41:06.3372+00:00
-- url     : https://prove2.me/theorems/80b76eda-b098-4a05-9fa9-16a3c0081072
-- title:
--   Theorem 5, p. 13 — exponential separation of global leakage in $\chi^2$-MI
-- statement:
--   Let $\mathbb G$ be a finite abelian group other than $\mathbb Z_2$ and $\mathbb Z_3$ (and non-trivial), i.e. $|\mathbb G|\ge4$, with the discrete $\sigma$-algebra. There is $M_0>0$ such that for every $M\in(0,M_0)$ there are leakage channels $\tau,\tau'$ (Markov kernels from $\mathbb G$ to a binary leakage space) with
--   $$I_{\chi^2}(S;L^{\tau})=I_{\chi^2}(S;L^{\tau'})=M$$
--   whose global $\chi^2$-MI, for i.i.d. leakage and $Z=S_0+\dots+S_d$, have different exponential rates: the limit below exists and
--   $$-\lim_{d\to\infty}\frac1d\log_2\frac{I_{\chi^2}(Z;X^{\tau})}{I_{\chi^2}(Z;X^{\tau'})}>0.$$
--
--   Fixing the local $\chi^2$-MI therefore does not fix the global exponent.
--
--   Differences from the source:
--
--   - encoding: 𝔾 ≠ ℤ2 nor ℤ3, a finite abelian group → 4 ≤ Fintype.card G; reason: the groups of order 2 and 3 are exactly ℤ2 and ℤ3; the trivial group has no non-trivial character and is excluded by the standing assumption I(S;L) > 0
--   - reading: "Let τ and τ′ be leakage channels such that I_χ²(S;L^τ) = I_χ²(S;L^τ′) = M … pairs of τ and τ′ exist", with M not quantified → ∃ M₀ > 0, ∀ M ∈ (0, M₀), ∃ τ τ′ with both local χ²-MI equal to M; reason: what the proof establishes (0 < M < min(G_q^{-2}, G_{q′}^{-2})); it implies the existence of one such pair and is not a weakening
--   - encoding: "different exponential rates; namely −lim (1/d) log ratio > 0" → ∃ r > 0 with Tendsto of −(1/d)·log₂(ratio) to r; reason: the limit exists and is positive
--   - encoding: leakage channels (unspecified leakage space) → Markov kernels G → Bool; reason: an existential claim; the proof's channels (Theorem 3) are binary, so naming the leakage space only makes the witnesses concrete
--   - reading: a channel without share index ("we may omit the subscript i, assuming that the leakages are i.i.d.", §2.1, p. 5) → one Markov kernel τ used for every share: globalJoint (fun _ => τ) d; reason: the paper's standing i.i.d. convention for unindexed statements
-- source:
--   Rei Ueno, A Spectral Theory of Local-to-Global Leakage, STOC 2027 submission #326 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/326.pdf, Theorem 5, p. 13

import Mathlib
import Definitions.Def_LeakageSpectral_Shannon_Divergences
import Definitions.Def_LeakageSpectral_Shannon_JointLaw
import Definitions.Def_LeakageSpectral_Shannon_ShareModel
import Definitions.Def_LeakageSpectral_Shannon_Supplement_Defs
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace LeakageSpectral.Shannon.Supplement

/-- Ueno, STOC 2027 submission #326, Theorem 5, p. 13: exponential separation of the global χ²-MI.
For a finite abelian group `G` other than `ℤ₂`, `ℤ₃` (and non-trivial), i.e. `|G| ≥ 4`, there is
`M₀ > 0` such that for every `M ∈ (0, M₀)` there are channels `τ`, `τ'` with
`I_χ²(S; L^τ) = I_χ²(S; L^τ') = M` for which `lim_{d→∞} -(1/d) log₂ (I_χ²(Z; X^τ) / I_χ²(Z; X^τ'))`
exists and is positive. -/
theorem theorem_5 {G : Type*} [AddCommGroup G] [Fintype G] [MeasurableSpace G]
    [DiscreteMeasurableSpace G] (hG : 4 ≤ Fintype.card G) :
    ∃ M₀ : ℝ, 0 < M₀ ∧ ∀ M : ℝ, 0 < M → M < M₀ →
      ∃ τ τ' : Kernel G Bool, IsMarkovKernel τ ∧ IsMarkovKernel τ' ∧
        chiSquareMI (localJoint τ) = M ∧ chiSquareMI (localJoint τ') = M ∧
        ∃ r : ℝ, 0 < r ∧
          Tendsto (fun d : ℕ => -(1 / (d : ℝ)) *
            Real.logb 2 (chiSquareMI (globalJoint (fun _ : ℕ => τ) d) /
              chiSquareMI (globalJoint (fun _ : ℕ => τ') d))) atTop (𝓝 r) := by sorry

end LeakageSpectral.Shannon.Supplement
