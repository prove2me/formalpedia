-- Prove2me | Theorems.Thm_GlobalTheory_SylvesterInertia_inlMap_injective
-- name    : GlobalTheory.SylvesterInertia.inlMap_injective
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T20:23:19.626791+00:00
-- url     : https://prove2.me/theorems/ea392689-a305-433c-be17-6727ec957da1
-- title:
--   Sylvester Inertia: inl Map injective
-- statement:
--   The Sylvester Inertia construction uses the inl Map injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/HasSignatureFstUniqueSylvester.lean#L23-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/HasSignatureFstUniqueSylvester.lean#L23-L24

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasSignatureFstUniqueSylvester
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.SylvesterInertia
open Matrix Module
open scoped ComplexOrder
variable {n : Type} [Fintype n] [DecidableEq n]

theorem GlobalTheory.SylvesterInertia.inlMap_injective (a b : ℕ) : Function.Injective (inlMap a b) := by sorry
