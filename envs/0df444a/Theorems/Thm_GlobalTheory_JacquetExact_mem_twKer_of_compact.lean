-- Prove2me | Theorems.Thm_GlobalTheory_JacquetExact_mem_twKer_of_compact
-- name    : GlobalTheory.JacquetExact.mem_twKer_of_compact
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T22:09:47.126731+00:00
-- url     : https://prove2.me/theorems/fef97909-7b42-437a-8c4b-99539fb4063d
-- title:
--   Jacquet Exact: mem tw Ker of compact
-- statement:
--   The Jacquet Exact construction uses the mem tw Ker of compact property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/InSupportOfIsSubquotient.lean#L47-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/InSupportOfIsSubquotient.lean#L47-L61

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LeviEmbMulSingle
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IwahoriProjSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_InSupportOfIsSubquotient
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.InertSupp GlobalTheory.IndefiniteRowSideFullHecke.TameConstituentPlaces ValuativeRel Matrix MeasureTheory
open GlobalTheory.IwahoriInj (Deep)
open GlobalTheory GlobalTheory.JacquetExact
variable {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
variable [TopologicalSpace G] [IsTopologicalGroup G]

theorem GlobalTheory.JacquetExact.mem_twKer_of_compact {σ : Representation ℂ G V} {τ : Representation ℂ G W} (hτ : IsSmooth τ)
    (f : σ.IntertwiningMap τ) (hf : Function.Injective f) {H : Subgroup G} (hH : IsCompact (H : Set G))
    {v : V} (hv : f v ∈ twKer τ H 1) : v ∈ twKer σ H 1 := by sorry
