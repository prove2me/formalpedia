-- Prove2me | Theorems.Thm_GlobalTheory_JacquetExact_isSubquotient_jac
-- name    : GlobalTheory.JacquetExact.isSubquotient_jac
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T22:09:23.980109+00:00
-- url     : https://prove2.me/theorems/6463df0e-4a61-4d5a-aa9b-1ded8cd1b261
-- title:
--   Jacquet Exact: is Subquotient jac
-- statement:
--   The Jacquet Exact construction uses the is Subquotient jac property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/InSupportOfIsSubquotient.lean#L91-L97
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/InSupportOfIsSubquotient.lean#L91-L97

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

theorem GlobalTheory.JacquetExact.isSubquotient_jac (e : (Σ a, Fin (d a)) ≃ n) {π : Representation ℂ (GL n k) V}
    {τ : Representation ℂ (GL n k) W} (hτ : IsSmooth τ) (h : IsSubquotient π τ) :
    IsSubquotient (jac e π) (jac e τ) := by sorry
