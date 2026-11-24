-- Prove2me | Theorems.Thm_GlobalTheory_T_isCO_prX_Cgrp_and_det_valuation_deltaR_eq_one
-- name    : GlobalTheory.T.isCO_prX_Cgrp_and_det_valuation_deltaR_eq_one
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T22:20:14.836571+00:00
-- url     : https://prove2.me/theorems/6c9bafb4-1170-4f79-8a3c-b769947e50ce
-- title:
--   T: is CO pr X Cgrp and det valuation delta R eq one
-- statement:
--   The T construction uses the is CO pr X Cgrp and det valuation delta R eq one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IsCOPrXCgrpStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IsCOPrXCgrpStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsCOPrXCgrp
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_FramePositiveSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsCOPrXCgrpStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix Topology GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.isCO_prX_Cgrp_and_det_valuation_deltaR_eq_one : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : Type) [Fintype n] [DecidableEq n] (c : ℕ) (J : Subgroup (GL (n ⊕ Fin c) k)), IsCO J → ∀ h : GL (n ⊕ Fin c) k, IsCO (prX (Cgrp J h)) ∧ ∀ g ∈ prX (Cgrp J h), valuation k ((Matrix.GeneralLinearGroup.det g : kˣ) : k) = 1 ∧ deltaR c g = 1 := by sorry
