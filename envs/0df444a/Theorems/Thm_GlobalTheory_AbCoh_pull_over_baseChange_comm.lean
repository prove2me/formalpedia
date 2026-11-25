-- Prove2me | Theorems.Thm_GlobalTheory_AbCoh_pull_over_baseChange_comm
-- name    : GlobalTheory.AbCoh.pull_over_baseChange_comm
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T15:31:45.272908+00:00
-- url     : https://prove2.me/theorems/1e79d7aa-512f-4d4a-963d-0ccc854008ed
-- title:
--   Ab Coh: pull over base Change comm
-- statement:
--   The Ab Coh construction uses the pull over base Change comm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/PullOverBaseChangeComm.lean#L13-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/PullOverBaseChangeComm.lean#L13-L30

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_AxesVanishingStructureSheafDegOne
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_PreUMono
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__AbelianHodgeDeRham_0e03413a4fcf6a02
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_StructureSheafCohomologyPullbackCompCupIdStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PullOverBaseChangeComm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.AbCoh

theorem GlobalTheory.AbCoh.pull_over_baseChange_comm : ∀ (R R' : Type) [CommRing R] [CommRing R'] (σ : R →+* R') (A Y : Over (Sp R)) (A' Y' : Over (Sp R')) (f : Y ⟶ A) (f' : Y' ⟶ A') (φ : A'.left ⟶ A.left) (ψ : Y'.left ⟶ Y.left) (hA : φ ≫ A.hom = A'.hom ≫ spMap σ) (hY : ψ ≫ Y.hom = Y'.hom ≫ spMap σ), f'.left ≫ φ = ψ ≫ f.left → (∀ x, pullHO1 hY (pO1 f x) = pO1 f' (pullHO1 hA x)) ∧ ∀ x, pullHO2 hY (structureSheafH2Pullback f x) = structureSheafH2Pullback f' (pullHO2 hA x) := by sorry
