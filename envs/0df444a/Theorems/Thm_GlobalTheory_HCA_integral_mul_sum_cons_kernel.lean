-- Prove2me | Theorems.Thm_GlobalTheory_HCA_integral_mul_sum_cons_kernel
-- name    : GlobalTheory.HCA.integral_mul_sum_cons_kernel
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T02:45:02.731928+00:00
-- url     : https://prove2.me/theorems/d7e0a2c0-2e08-4bfa-964b-b68b5d553bd1
-- title:
--   HCA: integral mul sum cons kernel
-- statement:
--   The HCA construction uses the integral mul sum cons kernel property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsDixmierMalliavinDecompProdExp.lean#L37-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsDixmierMalliavinDecompProdExp.lean#L37-L65

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsExpLieAlgebraComplexUnits
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_Casimir
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraRegularity_ExpHaar
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraInvariance_Compact
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavin
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_ParametricIntegral
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DixmierMalliavinFactorisationBasisStepStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousLeftTranslateBoundedDerivFunctional
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsDixmierMalliavinDecompProdExp
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.HCA MeasureTheory GroundTheory.Automorphic
open scoped ContDiff
open GlobalTheory GlobalTheory.HCA
variable {𝔸 : Type} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸]
  {G : Subgroup 𝔸ˣ} {𝔤 : Submodule ℝ 𝔸}

theorem GlobalTheory.HCA.integral_mul_sum_cons_kernel (h : IsExpLieAlgebra G 𝔤) {n N : ℕ} (X : Fin (n + 1) → 𝔤) {ε : ℝ}
    (hε : 0 ≤ ε) {u : ℝ → ℂ} (hu : Continuous u) (hus : tsupport u ⊆ Set.Icc (-ε) ε)
    {κ : Fin N → (Fin n → ℝ) → ℂ} (hκ : ∀ m, Continuous (κ m))
    (hκs : ∀ m, tsupport (κ m) ⊆ Metric.closedBall 0 ε) {Φ : Fin N → G → ℂ}
    (hΦ : ∀ m, Continuous (Φ m)) (Ψ : ℝ → ℂ)
    (hΨ : ∀ s, Ψ s = ∑ m, ∫ t', κ m t' * Φ m (h.expG (s • X 0) * h.prodExp (Fin.tail X) t')) :
    ∫ s, u s * Ψ s = ∑ m, ∫ t, u (t 0) * κ m (Fin.tail t) * Φ m (h.prodExp X t) := by sorry
