-- Prove2me | Theorems.Thm_GlobalTheory_TargetInequalityLemmas_target
-- name    : GlobalTheory.TargetInequalityLemmas.target
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T21:02:03.892511+00:00
-- url     : https://prove2.me/theorems/27a8d09d-b32f-4407-ba9b-cf95e0c537ef
-- title:
--   Target Inequality Lemmas: target
-- statement:
--   The Target Inequality Lemmas construction uses the target property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ImportsTerRest.lean#L23-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ImportsTerRest.lean#L23-L24

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ImportsTerRest
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.TargetInequalityLemmas
open Polynomial

theorem GlobalTheory.TargetInequalityLemmas.target : ∀ {R F K : Type} [inst : CommRing R] [IsDomain R] [inst_2 : Field F] [inst_3 : Algebra R F] [IsFractionRing R F] [inst_5 : Field K] [inst_6 : Algebra R K] [inst_7 : Algebra F K] [IsScalarTower R F K] (θ z : K), Membership.mem (Algebra.adjoin F (Singleton.singleton θ)) z → Exists fun (d : R) ↦ And (Ne d (0 : R)) (Membership.mem (Algebra.adjoin R (Singleton.singleton θ)) (HMul.hMul ((Algebra.algebraMap R K) d) z)) := by sorry
