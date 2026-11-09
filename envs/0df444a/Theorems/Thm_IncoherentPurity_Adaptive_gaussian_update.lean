-- Prove2me | Theorems.Thm_IncoherentPurity_Adaptive_gaussian_update
-- name    : IncoherentPurity.Adaptive.gaussian_update
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:58:30.908019+00:00
-- url     : https://prove2.me/theorems/0101dbef-d883-40bd-98ba-149a0a628120
-- title:
--   Lemma 6.9 — Gaussian posterior update
-- statement:
--   Condition on a current transcript with Gaussian posterior $N(m,C)$, where $C$ is any positive semidefinite covariance, and query a deterministic vector $a$ with fresh independent standard Gaussian noise. Set
--
--   $$b=Ca/\sqrt{1+a^\top Ca},\quad\xi=(Y-a^\top m)/\sqrt{1+a^\top Ca}.$$
--
--   Then $\xi$ has the standard Gaussian law, and for almost every response the posterior is $N(m+b\xi,C-bb^\top)$. Moreover $C-bb^\top\preceq C$. Singular covariance matrices are included; the posterior is computed by the actual Gaussian likelihood.
--
--   Differences from the source:
--   - encoding: matrix, probability and asymptotic notation in the paper → finite matrix coordinates, explicit experiment measures, and universal real constants; reason: the representations retain every source instance and clause; finite-moment conclusions prevent default-zero integrals
-- source:
--   Lee–Wadhwa, Optimal Purity Estimation with Incoherent Measurements, STOC 2027 submission #66 (2026), pinned source.pdf; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/66.pdf; SHA-256 7d80a6695c9c0b12bfa088a8f47d2a298b93f9fde9668867acfb4a95b19f03ce, Lemma 6.9, PDF p.21 = printed p.21

import Definitions.Def_IncoherentPurity_Adaptive_Estimators
import Definitions.Def_IncoherentPurity_Adaptive_Analytic

open MeasureTheory ProbabilityTheory Matrix
open scoped ENNReal ComplexOrder Matrix.Norms.Frobenius
set_option autoImplicit false
noncomputable section

namespace IncoherentPurity.Adaptive

/-- Lemma 6.9, PDF p.21, pinned source hash 7d80a6695c9c0b12bfa088a8f47d2a298b93f9fde9668867acfb4a95b19f03ce. -/
theorem gaussian_update {D : ℕ} (m a : Vec D) (C : Matrix (Fin D) (Fin D) ℝ) (hC : C.PosSemidef) :
  (responseLaw m C a).map (innovation m C a) = gaussianReal 0 1 ∧
  (∀ᵐ y ∂responseLaw m C a, bayesPosterior m C a y =
    gaussianVector (updateMean m C a y) (updateCov C a)) ∧
  (C - updateCov C a).PosSemidef := by sorry

end IncoherentPurity.Adaptive
