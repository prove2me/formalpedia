-- Prove2me | Theorems.Thm_GlobalTheory_OmAStab_isLocallyConstant_of_isOpen_ker
-- name    : GlobalTheory.OmAStab.isLocallyConstant_of_isOpen_ker
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T18:36:51.731424+00:00
-- url     : https://prove2.me/theorems/f70e9411-6eeb-40d5-b375-beddd7673cfe
-- title:
--   Om AStab: is Locally Constant of is Open ker
-- statement:
--   The Om AStab construction uses the is Locally Constant of is Open ker property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsOpenStabilizerSchwartzBruhat.lean#L12-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsOpenStabilizerSchwartzBruhat.lean#L12-L20

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FullRankSB
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_BernsteinUnitaryProductIrreducible
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NormalizedAbsCharacterization
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsOpenStabilizerSchwartzBruhat
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Topology GlobalTheory.SplitFlip GlobalTheory.SmGL GlobalTheory.WeilM
open GlobalTheory GlobalTheory.OmAStab
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem GlobalTheory.OmAStab.isLocallyConstant_of_isOpen_ker {G H : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [Group H] (χ : G →* H) (hχ : IsOpen (χ.ker : Set G)) : IsLocallyConstant χ := by sorry
