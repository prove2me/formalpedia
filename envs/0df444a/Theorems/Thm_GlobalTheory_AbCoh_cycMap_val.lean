-- Prove2me | Theorems.Thm_GlobalTheory_AbCoh_cycMap_val
-- name    : GlobalTheory.AbCoh.cycMap_val
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T14:58:56.687521+00:00
-- url     : https://prove2.me/theorems/595b7f94-7d28-41d0-8233-c058b7ca6087
-- title:
--   Ab Coh: cyc Map val
-- statement:
--   The Ab Coh construction uses the cyc Map val property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/NonemptyStructureSheafCohomologyModelOfQuasiIso.lean#L50-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/NonemptyStructureSheafCohomologyModelOfQuasiIso.lean#L50-L51

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_AxesVanishingStructureSheafDegOne
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__AbelianHodgeDeRham_0e03413a4fcf6a02
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsFiniteProjectiveComplexQuasiIso
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NonemptyStructureSheafCohomologyModelOfQuasiIso
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

theorem GlobalTheory.AbCoh.cycMap_val (i j : ℕ) (z : LinearMap.ker (dB K R' i j)) :
    (cycMap φ R' i j z).1 = (φ.f i).hom.baseChange R' z.1 := by sorry
