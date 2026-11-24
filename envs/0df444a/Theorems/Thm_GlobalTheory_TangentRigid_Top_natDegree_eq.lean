-- Prove2me | Theorems.Thm_GlobalTheory_TangentRigid_Top_natDegree_eq
-- name    : GlobalTheory.TangentRigid.Top.natDegree_eq
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T22:08:36.1738+00:00
-- url     : https://prove2.me/theorems/516b54d1-e28e-4c73-8941-0238416d04d2
-- title:
--   Top: nat Degree eq
-- statement:
--   The Top construction uses the nat Degree eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/FirstOrderRigid.lean#L51-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/FirstOrderRigid.lean#L51-L52

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_FirstOrderRigid
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open GlobalTheory GlobalTheory.TangentRigid
variable {k : Type} [Field k] {p q : k[X]} {d e : ℕ} {c c' : k}

theorem GlobalTheory.TangentRigid.Top.natDegree_eq (hp : Top p d 1) : p.natDegree = d := by sorry
