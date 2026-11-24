-- Prove2me | Theorems.Thm_GlobalTheory_JacquetExact_jacMap_injective
-- name    : GlobalTheory.JacquetExact.jacMap_injective
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T22:09:47.187094+00:00
-- url     : https://prove2.me/theorems/bd989333-93ec-4145-938f-7ac42bce2f55
-- title:
--   Jacquet Exact: jac Map injective
-- statement:
--   The Jacquet Exact construction uses the jac Map injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/InSupportOfIsSubquotient.lean#L71-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/InSupportOfIsSubquotient.lean#L71-L82

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

theorem GlobalTheory.JacquetExact.jacMap_injective (e : (Σ a, Fin (d a)) ≃ n) {σ : Representation ℂ (GL n k) V}
    {τ : Representation ℂ (GL n k) W} (hτ : IsSmooth τ) (f : σ.IntertwiningMap τ)
    (hf : Function.Injective f) : Function.Injective (jacMap e f) := by sorry
