-- Prove2me | Theorems.Thm_GlobalTheory_LatOrbGL_entries_of_matLat_le
-- name    : GlobalTheory.LatOrbGL.entries_of_matLat_le
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T17:58:42.486551+00:00
-- url     : https://prove2.me/theorems/3a7ad9d3-a8dd-44ee-a037-0d5b81ef97a8
-- title:
--   Lat Orb GL: entries of mat Lat le
-- statement:
--   The Lat Orb GL construction uses the entries of mat Lat le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MemGLintIffMatrixImageStandardLatticeEq.lean#L27-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MemGLintIffMatrixImageStandardLatticeEq.lean#L27-L39

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MemMatLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MemGLintIffMatrixImageStandardLatticeEq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial Matrix GlobalTheory.LatOrb
open GlobalTheory GlobalTheory.LatOrbGL
variable {K : Type} [Field K] (V : ValuationSubring K)

theorem GlobalTheory.LatOrbGL.entries_of_matLat_le {n : ℕ} (g : Matrix (Fin n) (Fin n) K)
    (hg : matLat V g (stdLat V n) ≤ stdLat V n) (i j : Fin n) : g i j ∈ V := by sorry
