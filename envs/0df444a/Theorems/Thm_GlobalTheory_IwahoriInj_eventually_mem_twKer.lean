-- Prove2me | Theorems.Thm_GlobalTheory_IwahoriInj_eventually_mem_twKer
-- name    : GlobalTheory.IwahoriInj.eventually_mem_twKer
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:10:51.951093+00:00
-- url     : https://prove2.me/theorems/59b4e244-02f1-410d-ba11-cb8a0041fc6e
-- title:
--   Iwahori Inj: eventually mem tw Ker
-- statement:
--   The Iwahori Inj construction uses the eventually mem tw Ker property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IsLocallyConstantOrbit.lean#L496-L507
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IsLocallyConstantOrbit.lean#L496-L507

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
variable [LinearOrder n]

theorem GlobalTheory.IwahoriInj.eventually_mem_twKer {v : V} (hv : v ∈ twKer π (unipB k n) 1) :
    ∀ᶠ m : ℕ in Filter.atTop, v ∈ twKer π (grp k (chamber_ray (n := n) m).1) 1 := by sorry
