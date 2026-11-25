-- Prove2me | Theorems.Thm_GlobalTheory_AbCoh_obRel_pullHO1
-- name    : GlobalTheory.AbCoh.obRel_pullHO1
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T14:57:54.124245+00:00
-- url     : https://prove2.me/theorems/b63f27d2-89d4-4bbe-80b6-e96eaf217f74
-- title:
--   Ab Coh: ob Rel pull HO1
-- statement:
--   The Ab Coh construction uses the ob Rel pull HO1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ConnectionCurvatureSumWedgeSemilinearPullback.lean#L36-L128
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ConnectionCurvatureSumWedgeSemilinearPullback.lean#L36-L128

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_AxesVanishingStructureSheafDegOne
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__AbelianHodgeDeRham_0e03413a4fcf6a02
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ConnectionCurvatureSumWedgeSemilinearPullback
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

theorem GlobalTheory.AbCoh.obRel_pullHO1 : ∀ (R R' : Type) [CommRing R] [CommRing R'] (X X' : Scheme.{0}) (s : X ⟶ Sp R) (s' : X' ⟶ Sp R') (σ : R →+* R') (φ : X' ⟶ X) (h : φ ≫ s = s' ≫ spMap σ) (x : HO1 s) (n : ℕ) (u v : Fin n → GlobForm s), ObRel (OAff s) x u v → ObRel (OAff s') (pullHO1 h x) (fun k ↦ GlobalTheory.CechDR.pullForm h (u k)) (fun k ↦ GlobalTheory.CechDR.pullForm h (v k)) := by sorry
