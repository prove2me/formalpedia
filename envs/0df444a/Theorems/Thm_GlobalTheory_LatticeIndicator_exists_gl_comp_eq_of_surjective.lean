-- Prove2me | Theorems.Thm_GlobalTheory_LatticeIndicator_exists_gl_comp_eq_of_surjective
-- name    : GlobalTheory.LatticeIndicator.exists_gl_comp_eq_of_surjective
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T12:12:56.549431+00:00
-- url     : https://prove2.me/theorems/d0cf1190-d568-55ab-a999-94ee05f35c93
-- title:
--   Lattice Indicator: exists gl comp eq of surjective
-- statement:
--   The Lattice Indicator construction uses the exists gl comp eq of surjective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/ExistsEqSumIndicatorOfRightInvariant.lean#L117-L134
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/ExistsEqSumIndicatorOfRightInvariant.lean#L117-L134

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsEqSumIndicatorOfRightInvariant
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open GlobalTheory
open GlobalTheory.LatticeIndicator

theorem GlobalTheory.LatticeIndicator.exists_gl_comp_eq_of_surjective {O Q n : Type*} [CommRing O] [IsLocalRing O]
    [AddCommGroup Q] [Module O Q] [Fintype n] [DecidableEq n] (a b : (n → O) →ₗ[O] Q)
    (ha : Function.Surjective a) (hb : Function.Surjective b) :
    ∃ g : GL n O, a = b ∘ₗ Matrix.toLin' (g : Matrix n n O) := by sorry
