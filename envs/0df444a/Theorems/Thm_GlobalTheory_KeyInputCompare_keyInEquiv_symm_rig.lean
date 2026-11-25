-- Prove2me | Theorems.Thm_GlobalTheory_KeyInputCompare_keyInEquiv_symm_rig
-- name    : GlobalTheory.KeyInputCompare.keyInEquiv_symm_rig
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T12:12:36.230968+00:00
-- url     : https://prove2.me/theorems/fc74dc57-36cf-4f66-bfab-5b14e59d725b
-- title:
--   Key Input Compare: key In Equiv symm rig
-- statement:
--   The Key Input Compare construction uses the key In Equiv symm rig property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/IsBaseChangeIffKeyPB.lean#L95-L95
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/IsBaseChangeIffKeyPB.lean#L95-L95

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

theorem GlobalTheory.KeyInputCompare.keyInEquiv_symm_rig (y : KeyInput R) : ((keyInEquiv R).symm y).rig = y.rig := by sorry

attribute [defeq] GlobalTheory.KeyInputCompare.keyInEquiv_symm_rig
