-- Prove2me | Theorems.Thm_GlobalTheory_WpFam_hasQ_gN
-- name    : GlobalTheory.WpFam.hasQ_gN
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T21:56:11.176477+00:00
-- url     : https://prove2.me/theorems/926dd545-94f7-499a-aea8-3ee955602bd9
-- title:
--   Wp Fam: has Q g N
-- statement:
--   The Wp Fam construction uses the has Q g N property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/WeierstrassConstantQExpansion.lean#L15-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/WeierstrassConstantQExpansion.lean#L15-L38

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ZetaActRefl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_WeierstrassConstantQExpansion
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open GlobalTheory.QFam GlobalTheory.WpFam
open GlobalTheory GlobalTheory.WpFam

theorem GlobalTheory.WpFam.hasQ_gN : ∀ (N : ℕ) [NeZero N], HasQ N gN (cG N) := by sorry
