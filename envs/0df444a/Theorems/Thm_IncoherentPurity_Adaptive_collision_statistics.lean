-- Prove2me | Theorems.Thm_IncoherentPurity_Adaptive_collision_statistics
-- name    : IncoherentPurity.Adaptive.collision_statistics
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:58:00.401632+00:00
-- url     : https://prove2.me/theorems/5e81c9a3-72da-4847-8882-ad2132926e34
-- title:
--   Lemma 3.3 — Fixed-basis collision statistics
-- statement:
--   Fix a state $\rho$ in dimension $d\ge1$, a unitary measurement basis $U$, and $s\ge2$ independent Born outcomes. Put $q_i=\langle i|U^*\rho U|i\rangle$ and $Q_j=\sum_iq_i^j$. The collision estimator is square integrable and satisfies
--
--   $$\mathbb E[\widehat Q\mid U]=Q_2,\qquad \operatorname{Var}(\widehat Q\mid U)=\frac{2(Q_2-Q_2^2)+4(s-2)(Q_3-Q_2^2)}{s(s-1)}.$$
--
--   This identifies the within-basis contribution to the batch estimator's variance.
--
--   Differences from the source:
--   - encoding: matrix, probability and asymptotic notation in the paper → finite matrix coordinates, explicit experiment measures, and universal real constants; reason: the representations retain every source instance and clause; finite-moment conclusions prevent default-zero integrals
--   - encoding: well-defined finite moments of the stated experiments → entrywise Integrable or MemLp 2 conclusions alongside the original moment or variance identities; reason: the experiments have bounded observations on the stated count domains; no additional hypothesis or source instance is imposed
-- source:
--   Lee–Wadhwa, Optimal Purity Estimation with Incoherent Measurements, STOC 2027 submission #66 (2026), pinned source.pdf; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/66.pdf; SHA-256 7d80a6695c9c0b12bfa088a8f47d2a298b93f9fde9668867acfb4a95b19f03ce, Lemma 3.3, PDF p.10 = printed p.10

import Definitions.Def_IncoherentPurity_Adaptive_Estimators
import Definitions.Def_IncoherentPurity_Adaptive_Analytic

open MeasureTheory ProbabilityTheory Matrix
open scoped ENNReal ComplexOrder Matrix.Norms.Frobenius
set_option autoImplicit false
noncomputable section

namespace IncoherentPurity.Adaptive

/-- Lemma 3.3, PDF p.10, pinned source hash 7d80a6695c9c0b12bfa088a8f47d2a298b93f9fde9668867acfb4a95b19f03ce. -/
theorem collision_statistics {d s : ℕ} (hd : 0 < d) (hs : 2 ≤ s) (ρ : State d) (U : Unitary d) :
  MemLp (collision (d:=d) (s:=s)) 2 (fixedLaw ρ.val U s) ∧
  (∫ a, collision a ∂fixedLaw ρ.val U s) = Q ρ.val U 2 ∧
  variance (collision (d:=d) (s:=s)) (fixedLaw ρ.val U s) =
    2 * (Q ρ.val U 2 - (Q ρ.val U 2)^2) / ((s : ℝ) * ((s : ℝ)-1)) +
    4 * ((s : ℝ)-2) * (Q ρ.val U 3 - (Q ρ.val U 2)^2) / ((s : ℝ) * ((s : ℝ)-1)) := by sorry

end IncoherentPurity.Adaptive
