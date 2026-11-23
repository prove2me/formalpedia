-- Prove2me | Theorems.Thm_GlobalTheory_IwahoriInj_exists_factor
-- name    : GlobalTheory.IwahoriInj.exists_factor
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:31:51.934898+00:00
-- url     : https://prove2.me/theorems/db90e3d9-a184-414e-a34c-5277d62317a1
-- title:
--   Iwahori Inj: exists factor
-- statement:
--   The Iwahori Inj construction uses the exists factor property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IsLocallyConstantOrbit.lean#L364-L377
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IsLocallyConstantOrbit.lean#L364-L377

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

theorem GlobalTheory.IwahoriInj.exists_factor (hg : Conc g) (hf : Chamber f) (hij : i ≠ j)
    (hfg : ∀ a b, ¬ (a = i ∧ b = j) → f a b = g a b) {p : GL n k} (hp : p ∈ grp k hg)
    (h : ¬ Deep 1 (p.val j j)) : ∃ y : k, Deep (g i j) y ∧ ∃ b ∈ grp k hf.1, p = elem hij y * b := by sorry
