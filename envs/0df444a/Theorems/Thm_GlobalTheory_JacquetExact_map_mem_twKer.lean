-- Prove2me | Theorems.Thm_GlobalTheory_JacquetExact_map_mem_twKer
-- name    : GlobalTheory.JacquetExact.map_mem_twKer
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T22:10:11.774083+00:00
-- url     : https://prove2.me/theorems/5b2b9d1c-860d-4cb2-ad86-63801ec313f5
-- title:
--   Jacquet Exact: map mem tw Ker
-- statement:
--   The Jacquet Exact construction uses the map mem tw Ker property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/InSupportOfIsSubquotient.lean#L37-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/InSupportOfIsSubquotient.lean#L37-L43

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

theorem GlobalTheory.JacquetExact.map_mem_twKer {σ : Representation ℂ G V} {τ : Representation ℂ G W} (f : σ.IntertwiningMap τ)
    {H : Subgroup G} {v : V} (hv : v ∈ twKer σ H 1) : f v ∈ twKer τ H 1 := by sorry
