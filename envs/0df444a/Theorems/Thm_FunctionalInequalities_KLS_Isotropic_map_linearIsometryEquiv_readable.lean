-- Prove2me | Theorems.Thm_FunctionalInequalities_KLS_Isotropic_map_linearIsometryEquiv_readable
-- name    : FunctionalInequalities.KLS.Isotropic.map_linearIsometryEquiv_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:16:45.272984+00:00
-- url     : https://prove2.me/theorems/2a04e022-1e2a-44a3-9511-86cbce831c79
-- title:
--   Isotropy Under a Linear Isometric Equivalence
-- statement:
--   This statement asserts that isotropy is preserved by a linear isometric equivalence.
--
--   Let $E$ and $F$ be finite-dimensional complete real inner product spaces equipped with their Borel measurable structures. Let $\nu$ be an isotropic probability measure on $E$, and let $\varphi:E\to F$ be a surjective linear isometry. Here isotropy (`KLS.Isotropic`) means finite second moment, zero mean, and identity centered covariance.
--
--   The pushforward probability measure is isotropic:
--   $$
--   \operatorname{Isotropic}(\varphi_\#\nu).
--   $$
--   This permits isotropic laws to be transported between isometrically equivalent coordinate spaces.
--
--   **Formalization Note** The pushforward is `ProbabilityMeasure.map`, using the measurability supplied by continuity of $\varphi$. No positive-dimension assumption is required.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.KLS`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem Isotropic.map_linearIsometryEquiv {ν : ProbabilityMeasure E}
--       (hν : Isotropic ν) (φ : E ≃ₗᵢ[ℝ] F) :
--       Isotropic (ν.map φ.continuous.measurable.aemeasurable)
--   ```
--
--   **Module navigation**
--
--   Module: [`KLS/Isotropic`](https://prove2.me/theorems/b8da0fa3-d27f-46ae-b3b9-8c204df57e02).
--
--   Next: [`integral_fderiv_mul_fderiv_eq_inner_of_isotropic_map`](https://prove2.me/theorems/5232fd28-307b-473d-a267-0276d096b8b7).
--
--   [Source excerpt, lines 86–88](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/Isotropic.lean#L86-L88) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/Isotropic.lean#L84-L133 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.Isotropic`, declaration `FunctionalInequalities.KLS.Isotropic.map_linearIsometryEquiv`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_Isotropic

open MeasureTheory
variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {E F : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
variable [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F]

theorem FunctionalInequalities.KLS.Isotropic.map_linearIsometryEquiv_readable {ν : ProbabilityMeasure E}
    (hν : Isotropic ν) (φ : E ≃ₗᵢ[ℝ] F) :
    Isotropic (ν.map φ.continuous.measurable.aemeasurable) := by sorry
