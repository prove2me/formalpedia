-- Prove2me | Theorems.Thm_GlobalTheory_CechDR_hasLoc_OAff
-- name    : GlobalTheory.CechDR.hasLoc_OAff
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T16:12:59.207845+00:00
-- url     : https://prove2.me/theorems/4adecd2d-1caa-4630-b81d-b6c2c9335b44
-- title:
--   Cech DR: has Loc OAff
-- statement:
--   The Cech DR construction uses the has Loc OAff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HasLocOAff.lean#L12-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HasLocOAff.lean#L12-L44

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ComparisonMemCechHodgeFiltration
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_VanishingH1InvertingMorphisms
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasLocOAff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry KaehlerDifferential ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.CechDR
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CechDR

theorem GlobalTheory.CechDR.hasLoc_OAff : ∀ {R' : Type} [CommRing R'] {X' : Scheme.{0}} (s' : X' ⟶ Sp R'),
    Desc.HasLoc (OAff s') := by sorry
