-- Prove2me | Theorems.Thm_GroundTheory_Brauer_exists_isSimpleModule_algEquiv_end
-- name    : GroundTheory.Brauer.exists_isSimpleModule_algEquiv_end
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T23:36:43.457499+00:00
-- url     : https://prove2.me/theorems/2c329c7e-551b-409b-ac36-0b6974e1e775
-- title:
--   Brauer: exists is Simple Module alg Equiv end
-- statement:
--   The Brauer construction uses the exists is Simple Module alg Equiv end property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/Brauer/IsBrauerEquivalentIffNonemptyAlgEquiv.lean#L291-L296
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/Brauer/IsBrauerEquivalentIffNonemptyAlgEquiv.lean#L291-L296

import Mathlib
import Definitions.Def_GroundTheory_Brauer_TensorSimple
import Definitions.Def_GroundTheory_Brauer_IsBrauerEquivalentIffNonemptyAlgEquiv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Brauer
open TensorProduct
universe u v w
variable {K : Type u} [Field K]

theorem GroundTheory.Brauer.exists_isSimpleModule_algEquiv_end {R : Type v} [Ring R] [Algebra K R] {D : Type w}
    [DivisionRing D] [Algebra K D] {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (e : R ≃ₐ[K] Matrix ι ι D) :
    ∃ I : Ideal R, IsSimpleModule R I ∧ Nonempty (Module.End R I ≃ₐ[K] Dᵐᵒᵖ) := by sorry
