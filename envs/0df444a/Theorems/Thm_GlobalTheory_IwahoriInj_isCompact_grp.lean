-- Prove2me | Theorems.Thm_GlobalTheory_IwahoriInj_isCompact_grp
-- name    : GlobalTheory.IwahoriInj.isCompact_grp
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T17:28:22.57032+00:00
-- url     : https://prove2.me/theorems/68c65d57-efdb-4ce0-84ca-93d7ef4b798a
-- title:
--   Iwahori Inj: is Compact grp
-- statement:
--   The Iwahori Inj construction uses the is Compact grp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IsLocallyConstantOrbit.lean#L296-L311
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IsLocallyConstantOrbit.lean#L296-L311

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

theorem GlobalTheory.IwahoriInj.isCompact_grp {f : n → n → ℤ} (hf : Conc f) : IsCompact (grp k hf : Set (GL n k)) := by sorry
