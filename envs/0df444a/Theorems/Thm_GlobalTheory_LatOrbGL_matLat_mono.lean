-- Prove2me | Theorems.Thm_GlobalTheory_LatOrbGL_matLat_mono
-- name    : GlobalTheory.LatOrbGL.matLat_mono
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T17:59:01.562063+00:00
-- url     : https://prove2.me/theorems/ab6617cf-33df-4525-bb21-d3693539771a
-- title:
--   Lat Orb GL: mat Lat mono
-- statement:
--   The Lat Orb GL construction uses the mat Lat mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MemGLintIffMatrixImageStandardLatticeEq.lean#L41-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MemGLintIffMatrixImageStandardLatticeEq.lean#L41-L42

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

theorem GlobalTheory.LatOrbGL.matLat_mono {n : ℕ} (g : Matrix (Fin n) (Fin n) K) {M N : Submodule V (Fin n → K)}
    (h : M ≤ N) : matLat V g M ≤ matLat V g N := by sorry
