-- Prove2me | Theorems.Thm_GlobalTheory_LatOrb_mem_GLint_iff_matLat_std
-- name    : GlobalTheory.LatOrb.mem_GLint_iff_matLat_std
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T17:59:03.082271+00:00
-- url     : https://prove2.me/theorems/3e14f464-0b7b-48f1-b082-439067779d22
-- title:
--   Lat Orb: mem GLint iff mat Lat std
-- statement:
--   The Lat Orb construction uses the mem GLint iff mat Lat std property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MemGLintIffMatrixImageStandardLatticeEq.lean#L48-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MemGLintIffMatrixImageStandardLatticeEq.lean#L48-L80

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
open GlobalTheory.LatOrbGL

theorem GlobalTheory.LatOrb.mem_GLint_iff_matLat_std :
    ∀ {K : Type} [Field K] (V : ValuationSubring K) (n : ℕ) (k : GL (Fin n) K),
    k ∈ Formalism.UG.GLint (Fin n) V.toSubring ↔ matLat V k.val (stdLat V n) = stdLat V n := by sorry
