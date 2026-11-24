-- Prove2me | Theorems.Thm_GlobalTheory_KeyKa_torsSq_map
-- name    : GlobalTheory.KeyKa.torsSq_map
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T09:42:02.137192+00:00
-- url     : https://prove2.me/theorems/63899c6d-2ea5-4d7f-ae6e-5871d150d0af
-- title:
--   Key Ka: tors Sq map
-- statement:
--   The Key Ka construction uses the tors Sq map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/TorsSqMap.lean#L7-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/TorsSqMap.lean#L7-L19

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_DegProd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_TorsSqMap
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.KeyKa
open GlobalTheory GlobalTheory.KeyKa

theorem GlobalTheory.KeyKa.torsSq_map : ∀ (R Ix : Type) [CommRing R] [Fintype Ix] [DecidableEq Ix] (deg : Ix → ℕ) (D : Matrix Ix Ix R) (R' : Type) [CommRing R'] (f : R →+* R') (t : R), TorsSq deg D t → TorsSq deg (D.map f) (f t) := by sorry
