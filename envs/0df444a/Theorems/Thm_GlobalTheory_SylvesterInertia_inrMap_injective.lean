-- Prove2me | Theorems.Thm_GlobalTheory_SylvesterInertia_inrMap_injective
-- name    : GlobalTheory.SylvesterInertia.inrMap_injective
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T20:23:28.421783+00:00
-- url     : https://prove2.me/theorems/fea2cee8-f949-4f14-bb7c-e126cbd03ef2
-- title:
--   Sylvester Inertia: inr Map injective
-- statement:
--   The Sylvester Inertia construction uses the inr Map injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/HasSignatureFstUniqueSylvester.lean#L26-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/HasSignatureFstUniqueSylvester.lean#L26-L27

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

theorem GlobalTheory.SylvesterInertia.inrMap_injective (a b : ℕ) : Function.Injective (inrMap a b) := by sorry
