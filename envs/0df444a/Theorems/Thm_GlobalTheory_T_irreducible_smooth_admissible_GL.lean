-- Prove2me | Theorems.Thm_GlobalTheory_T_irreducible_smooth_admissible_GL
-- name    : GlobalTheory.T.irreducible_smooth_admissible_GL
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T12:02:51.612285+00:00
-- url     : https://prove2.me/theorems/09fcf4cc-3d49-5621-8ac1-89d67a70cc73
-- title:
--   T: irreducible smooth admissible GL
-- statement:
--   The T construction uses the irreducible smooth admissible GL property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/IrreducibleSmoothAdmissibleGLStatement.lean#L5-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/IrreducibleSmoothAdmissibleGLStatement.lean#L5-L6

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_IrreducibleSmoothAdmissibleGL
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_HasFiniteLengthOfIsIrreducible
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_IrreducibleSmoothAdmissibleGLStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000

theorem GlobalTheory.T.irreducible_smooth_admissible_GL : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], GlobalTheory.SmGL.IrreducibleAdmissible k := by sorry
