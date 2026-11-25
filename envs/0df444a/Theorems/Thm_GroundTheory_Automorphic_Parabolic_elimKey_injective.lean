-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Parabolic_elimKey_injective
-- name    : GroundTheory.Automorphic.Parabolic.elimKey_injective
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T11:18:42.422269+00:00
-- url     : https://prove2.me/theorems/0ecd55da-9044-5562-9e5b-571e351ad7d3
-- title:
--   Parabolic: elim Key injective
-- statement:
--   The Parabolic construction uses the elim Key injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/IwahoriFactorization.lean#L22-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/IwahoriFactorization.lean#L22-L24

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_InductionParabolic
import Definitions.Def_GroundTheory_AutomorphicForms_AffineBruhat
import Definitions.Def_GroundTheory_AutomorphicForms_IwahoriFactorization
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.Parabolic
open Matrix Iwasawa GLnLocal ValuativeRel Topology Filter Set
variable {F : Type*} [Field F] {n : ℕ} {α : Type*} [LinearOrder α] (β : Fin n → α)
variable {β}
omit [LinearOrder α]

theorem GroundTheory.Automorphic.Parabolic.elimKey_injective : Function.Injective (elimKey β) := by sorry
