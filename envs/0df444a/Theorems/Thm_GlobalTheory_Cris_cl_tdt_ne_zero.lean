-- Prove2me | Theorems.Thm_GlobalTheory_Cris_cl_tdt_ne_zero
-- name    : GlobalTheory.Cris.cl_tdt_ne_zero
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T12:02:58.8326+00:00
-- url     : https://prove2.me/theorems/4f839639-d580-5bbe-98e8-7c7f350ca00e
-- title:
--   Cris: cl tdt ne zero
-- statement:
--   The Cris construction uses the cl tdt ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/CrystallineConnectionFormCoboundaryZero.lean#L214-L249
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/CrystallineConnectionFormCoboundaryZero.lean#L214-L249

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_Pullback1MemHodgeFiltration
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_CrystallineConnectionFormCoboundaryZero
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
open CategoryTheory AlgebraicGeometry DividedPowers
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GlobalTheory GlobalTheory.Cris
open CatCoh
variable {R : Type} [CommRing R] {I : Ideal R} {X : Scheme.{0}}
open Polynomial

theorem GlobalTheory.Cris.cl_tdt_ne_zero [Nontrivial R] (h2 : (2 : R) = 0) : Form.cl _ (tdt R) ≠ 0 := by sorry
