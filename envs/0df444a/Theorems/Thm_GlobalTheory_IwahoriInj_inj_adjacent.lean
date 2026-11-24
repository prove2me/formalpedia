-- Prove2me | Theorems.Thm_GlobalTheory_IwahoriInj_inj_adjacent
-- name    : GlobalTheory.IwahoriInj.inj_adjacent
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T17:22:17.165348+00:00
-- url     : https://prove2.me/theorems/f3dd9b30-d1d3-4d55-83b1-09fa7785ecdf
-- title:
--   Iwahori Inj: inj adjacent
-- statement:
--   The Iwahori Inj construction uses the inj adjacent property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IsLocallyConstantOrbit.lean#L381-L418
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IsLocallyConstantOrbit.lean#L381-L418

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_T2SpaceGeneralLinearGroup
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_TwistedKernelFixed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsLocallyConstantOrbit
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL ValuativeRel MeasureTheory
open GlobalTheory GlobalTheory.IwahoriInj
open Matrix
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n : Type} [Fintype n] [DecidableEq n]
variable {g f f' : n → n → ℤ} {i j : n}
variable {V : Type} [AddCommGroup V] [Module ℂ V] {π : Representation ℂ (GL n k) V}

theorem GlobalTheory.IwahoriInj.inj_adjacent (hπ : IsSmooth π) (hg : Conc g) (hf : Chamber f) (hf' : Chamber f') (hij : i ≠ j)
    (h1 : f i j = g i j + 1) (h2 : ∀ a b, ¬ (a = i ∧ b = j) → f a b = g a b)
    (h3 : f' j i = g j i + 1) (h4 : ∀ a b, ¬ (a = j ∧ b = i) → f' a b = g a b) :
    Inj π (grp k hf.1) (grp k hf'.1) := by sorry
