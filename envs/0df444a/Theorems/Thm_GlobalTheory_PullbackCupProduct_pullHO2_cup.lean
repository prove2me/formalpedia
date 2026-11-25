-- Prove2me | Theorems.Thm_GlobalTheory_PullbackCupProduct_pullHO2_cup
-- name    : GlobalTheory.PullbackCupProduct.pullHO2_cup
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T14:58:36.493046+00:00
-- url     : https://prove2.me/theorems/5561b8e2-122e-427d-ac49-4f4fd92ba810
-- title:
--   Pullback Cup Product: pull HO2 cup
-- statement:
--   The Pullback Cup Product construction uses the pull HO2 cup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/PullCupOfBijective.lean#L35-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/PullCupOfBijective.lean#L35-L39

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_AxesVanishingStructureSheafDegOne
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__AbelianHodgeDeRham_0e03413a4fcf6a02
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PullCupOfBijective
import Theorems.Thm_GlobalTheory_CechDR_IsPull1_cup

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
open CategoryTheory
open GlobalTheory GlobalTheory.PullbackCupProduct
open GlobalTheory.CatCoh
universe u v u' v' u'' v''
variable {R R' : Type} [CommRing R] [CommRing R'] {X X' : AlgebraicGeometry.Scheme}
  {s : X ⟶ ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp R} {s' : X' ⟶ ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp R'} {σ : R →+* R'}
  {φ : X' ⟶ X}

theorem GlobalTheory.PullbackCupProduct.pullHO2_cup (h : φ ≫ s = s' ≫ ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap σ) (a b : GlobalTheory.CechDR.HO1 s) :
    GlobalTheory.AbCoh.pullHO2 h (cup _ a b) = cup _ (GlobalTheory.CechDR.pullHO1 h a) (GlobalTheory.CechDR.pullHO1 h b) := by sorry
