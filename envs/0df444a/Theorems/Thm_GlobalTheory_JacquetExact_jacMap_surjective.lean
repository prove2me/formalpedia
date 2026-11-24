-- Prove2me | Theorems.Thm_GlobalTheory_JacquetExact_jacMap_surjective
-- name    : GlobalTheory.JacquetExact.jacMap_surjective
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T22:09:05.935547+00:00
-- url     : https://prove2.me/theorems/bee12863-c2d7-4873-a6f4-8f021a22b450
-- title:
--   Jacquet Exact: jac Map surjective
-- statement:
--   The Jacquet Exact construction uses the jac Map surjective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/InSupportOfIsSubquotient.lean#L84-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/InSupportOfIsSubquotient.lean#L84-L89

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
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n : Type} [Fintype n] [DecidableEq n] {V W : Type} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup W] [Module ℂ W] {s : ℕ} {d : Fin s → ℕ}

theorem GlobalTheory.JacquetExact.jacMap_surjective (e : (Σ a, Fin (d a)) ≃ n) {σ : Representation ℂ (GL n k) V}
    {τ : Representation ℂ (GL n k) W} (f : σ.IntertwiningMap τ)
    (hf : Function.Surjective f) : Function.Surjective (jacMap e f) := by sorry
