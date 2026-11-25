-- Prove2me | Theorems.Thm_GlobalTheory_AbCoh_pairToPre_pull2_pairPull
-- name    : GlobalTheory.AbCoh.pairToPre_pull2_pairPull
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T15:11:33.844142+00:00
-- url     : https://prove2.me/theorems/bcce99e9-4f17-5ba5-96f7-b49b55a7930a
-- title:
--   Ab Coh: pair To Pre pull2 pair Pull
-- statement:
--   The Ab Coh construction uses the pair To Pre pull2 pair Pull property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CocyclePullbackIffPreimageAffineHom.lean#L76-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CocyclePullbackIffPreimageAffineHom.lean#L76-L79

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_AxesVanishingStructureSheafDegOne
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_PreUMono
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__AbelianHodgeDeRham_0e03413a4fcf6a02
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CocyclePullbackIffPreimageAffineHom
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
variable {R R' : Type} [CommRing R] [CommRing R'] {X X' : Scheme.{0}} {φ : X' ⟶ X} [IsAffineHom φ]
  {s : X ⟶ Sp R} {s' : X' ⟶ Sp R'} {σ : R →+* R'}
variable (h : φ ≫ s = s' ≫ spMap σ)

theorem GlobalTheory.AbCoh.pairToPre_pull2_pairPull (y : HO2 s) :
    (pairToPre φ s').pull2 ((pairPull h).pull2 y) = (preCoef h).pull2 y := by sorry
