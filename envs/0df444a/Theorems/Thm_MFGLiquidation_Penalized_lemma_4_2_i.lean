-- Prove2me | Theorems.Thm_MFGLiquidation_Penalized_lemma_4_2_i
-- name    : MFGLiquidation.Penalized.lemma_4_2_i
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T02:31:19.910227+00:00
-- url     : https://prove2.me/theorems/2ddb383a-8840-43cc-9be9-9b764dca0639
-- title:
--   Lemma 4.2 (first condition) — if η is deterministic, Assumption 4.1 holds
-- statement:
--   Assume Assumption 2.3, and let $(A,Z^A)$ be the solution of the singular Riccati BSDE
--   $$-dA_t=\Big(2\lambda_t-\frac{A_t^2}{2\eta_t}\Big)dt-Z^A_t\,d\widetilde W_t,\qquad A_T=+\infty .$$
--   If the temporary impact $\eta$ is deterministic, i.e. $\eta_t(\omega)$ does not depend on $\omega$, then Assumption 4.1 holds: there is a constant $C$ such that almost surely, for all $0\le r\le s<T$,
--   $$\exp\Big(-\int_r^s\frac{A_u}{2\eta_u}\,du\Big)\le C\,\frac{T-s}{T-r}.$$
--
--   This is the simplest sufficient condition for Assumption 4.1, and shows that the hypothesis of Lemma 4.5 and Theorem 4.6 can be met.
--
--   **Formalization Note.** Only the first of the three conditions of Lemma 4.2 is stated; the other two rest on [3, Lemma 5.1]. Assumption 2.3 is assumed throughout the paper (p. 8); the appendix itself assumes $\lambda,\eta,1/\eta$ bounded, which Assumption 2.3 implies. "Deterministic" is read pointwise: $\eta_t(\omega)=\eta_t(\omega')$ for all $t,\omega,\omega'$.
-- source:
--   Fu, Graewe, Horst, Popier, A Mean Field Game of Optimal Portfolio Liquidation, arXiv:1804.04911v3, pp. 24–25, Lemma 4.2 (first bullet); proof p. 33

import Mathlib
import Definitions.Def_Peng1990_SMP_Stochastic
import Definitions.Def_MFGLiquidation_Penalized_Setting
import Definitions.Def_MFGLiquidation_Penalized_Decoupled
open MeasureTheory ProbabilityTheory Filter Topology Peng1990.SMP
open scoped ENNReal NNReal

namespace MFGLiquidation.Penalized

/-- Lemma 4.2, first condition (p. 24; proof p. 33): if `η` is deterministic, Assumption 4.1
holds for the singular Riccati solution `A` of Lemma A.1. -/
theorem lemma_4_2_i {Ω : Type*} [MeasurableSpace Ω] {k : ℕ} {P : Measure Ω}
    [IsProbabilityMeasure P] {D : Data Ω k} (hD : D.Standing P) (hA : D.Assumption23 P hD)
    (A : ℝ≥0 → Ω → ℝ) (ZA : Fin (k + 1) → ℝ≥0 → Ω → ℝ) (hRic : IsSingularRiccati hD A ZA)
    (hdet : ∀ (t : ℝ≥0) (ω ω' : Ω), D.η t ω = D.η t ω') :
    Assumption41 hD A := by sorry

end MFGLiquidation.Penalized
