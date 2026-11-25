-- Prove2me | Theorems.Thm_GlobalTheory_AbCoh_exact_comp
-- name    : GlobalTheory.AbCoh.exact_comp
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T15:04:21.389502+00:00
-- url     : https://prove2.me/theorems/1ec2f1e4-86f5-51e0-9640-e085e23c89ae
-- title:
--   Ab Coh: exact comp
-- statement:
--   The Ab Coh construction uses the exact comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/NonemptyStructureSheafCohomologyModelOfQuasiIso.lean#L60-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/NonemptyStructureSheafCohomologyModelOfQuasiIso.lean#L60-L82

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_AxesVanishingStructureSheafDegOne
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__AbelianHodgeDeRham_0e03413a4fcf6a02
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsFiniteProjectiveComplexQuasiIso
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NonemptyStructureSheafCohomologyModelOfQuasiIso
import Theorems.Thm_GlobalTheory_CechDR_SemiHom_comp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.AbCoh
variable {R : Type} [CommRing R] {K C : CochainComplex (ModuleCat.{0} R) ℕ} (φ : K ⟶ C)
  (R' : Type) [CommRing R'] [Algebra R R']

theorem GlobalTheory.AbCoh.exact_comp {H : Type} [AddCommGroup H] [Module R' H] (i j k : ℕ)
    (θ : LinearMap.ker (dB C R' j k) →ₗ[R'] H) (hs : Function.Surjective θ)
    (hk : ∀ z, θ z = 0 ↔ z.1 ∈ LinearMap.range (dB C R' i j))
    (surj : ∀ c, dB C R' j k c = 0 → ∃ (c' : R' ⊗[R] C.X i) (k' : R' ⊗[R] K.X j),
      dB K R' j k k' = 0 ∧ dB C R' i j c' + (φ.f j).hom.baseChange R' k' = c)
    (inj : ∀ (k' : R' ⊗[R] K.X j) (c : R' ⊗[R] C.X i), dB K R' j k k' = 0 →
      (φ.f j).hom.baseChange R' k' = dB C R' i j c → k' ∈ LinearMap.range (dB K R' i j)) :
    Function.Surjective (θ.comp (cycMap φ R' j k)) ∧
      ∀ z, θ.comp (cycMap φ R' j k) z = 0 ↔ z.1 ∈ LinearMap.range (dB K R' i j) := by sorry
