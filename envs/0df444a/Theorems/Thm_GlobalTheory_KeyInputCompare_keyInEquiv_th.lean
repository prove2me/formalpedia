-- Prove2me | Theorems.Thm_GlobalTheory_KeyInputCompare_keyInEquiv_th
-- name    : GlobalTheory.KeyInputCompare.keyInEquiv_th
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T12:14:06.734643+00:00
-- url     : https://prove2.me/theorems/3249c8d5-6d8c-5b9b-9e49-12b71ad52a7b
-- title:
--   Key Input Compare: key In Equiv th
-- statement:
--   The Key Input Compare construction uses the key In Equiv th property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/IsBaseChangeIffKeyPB.lean#L92-L92
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/IsBaseChangeIffKeyPB.lean#L92-L92

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasis
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_CMModuli_PolarizationCorrespondence
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_IsBaseChangeIffKeyPB
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
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.IndefiniteRowSideFullHecke.PolarizationCorrespondence
open GlobalTheory GlobalTheory.KeyInputCompare
variable {R R' : Type} [CommRing R] [CommRing R']

theorem GlobalTheory.KeyInputCompare.keyInEquiv_th (x : KeyIn R) : (keyInEquiv R x).th = x.th := by sorry

attribute [defeq] GlobalTheory.KeyInputCompare.keyInEquiv_th
