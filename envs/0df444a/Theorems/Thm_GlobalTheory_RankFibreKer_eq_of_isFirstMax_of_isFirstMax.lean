-- Prove2me | Theorems.Thm_GlobalTheory_RankFibreKer_eq_of_isFirstMax_of_isFirstMax
-- name    : GlobalTheory.RankFibreKer.eq_of_isFirstMax_of_isFirstMax
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T19:14:01.260239+00:00
-- url     : https://prove2.me/theorems/0e2eafe3-52a1-4a34-840d-29d36de3f08d
-- title:
--   Rank Fibre Ker: eq of is First Max of is First Max
-- statement:
--   The Rank Fibre Ker construction uses the eq of is First Max of is First Max property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SectionInverseIntoSlice.lean#L7-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SectionInverseIntoSlice.lean#L7-L14

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_OmAOneApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SectionInverseIntoSlice
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory ValuativeRel GlobalTheory.SplitFlip GlobalTheory.SmGL GlobalTheory.WeilM GlobalTheory.RankFibre GlobalTheory.SplitWeil GlobalTheory.RankFibreKer
open GlobalTheory GlobalTheory.RankFibreKer

theorem GlobalTheory.RankFibreKer.eq_of_isFirstMax_of_isFirstMax {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {a d : ℕ} {Y : Matrix (Fin a) (Fin d) k} {J J' : Fin a ↪ Fin d} (h : IsFirstMax Y J) (h' : IsFirstMax Y J') :
    J = J' := by sorry
