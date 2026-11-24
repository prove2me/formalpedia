-- Prove2me | Theorems.Thm_GlobalTheory_RankFibreKer_minor_mul
-- name    : GlobalTheory.RankFibreKer.minor_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:12:51.933066+00:00
-- url     : https://prove2.me/theorems/916b8b8b-68a9-4d52-9d9e-e6e97f94d995
-- title:
--   Rank Fibre Ker: minor mul
-- statement:
--   The Rank Fibre Ker construction uses the minor mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/OmAOneApply.lean#L47-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/OmAOneApply.lean#L47-L50

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FullRankSB
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_BernsteinUnitaryProductIrreducible
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_OmAOneApply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix MeasureTheory ValuativeRel GlobalTheory.SplitFlip GlobalTheory.SmGL GlobalTheory.WeilM GlobalTheory.RankFibre GlobalTheory.SplitWeil
open GlobalTheory GlobalTheory.RankFibreKer
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem GlobalTheory.RankFibreKer.minor_mul {a d : ℕ} (g : Matrix (Fin a) (Fin a) k) (Y : Matrix (Fin a) (Fin d) k) (J : Fin a ↪ Fin d) :
    minor (g * Y) J = g.det * minor Y J := by sorry
