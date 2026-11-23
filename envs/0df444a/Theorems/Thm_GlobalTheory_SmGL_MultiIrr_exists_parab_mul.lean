-- Prove2me | Theorems.Thm_GlobalTheory_SmGL_MultiIrr_exists_parab_mul
-- name    : GlobalTheory.SmGL.MultiIrr.exists_parab_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:37:05.441811+00:00
-- url     : https://prove2.me/theorems/f4903f1d-791f-4978-838a-55cea311db8f
-- title:
--   Multi Irr: exists parab mul
-- statement:
--   The Multi Irr construction uses the exists parab mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IsIrreducibleIffOfLinearEquiv.lean#L356-L360
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IsIrreducibleIffOfLinearEquiv.lean#L356-L360

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_BernsteinUnitaryProductIrreducible
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsLocallyConstantModulus
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LowerEquivUpperSwap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsIrreducibleIffOfLinearEquiv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL ValuativeRel Matrix
open scoped TensorProduct
open GlobalTheory GlobalTheory.SmGL GlobalTheory.SmGL.MultiIrr
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {a b n a' b' n' : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [Fintype n] [DecidableEq n]
  [Fintype a'] [DecidableEq a'] [Fintype b'] [DecidableEq b'] [Fintype n'] [DecidableEq n']
  {V W U : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] [AddCommGroup U] [Module ℂ U]

theorem GlobalTheory.SmGL.MultiIrr.exists_parab_mul {α : Type} {m : α → Type} [Fintype α] [LinearOrder α] [∀ i, Fintype (m i)]
    [∀ i, DecidableEq (m i)] (e : (Σ i, m i) ≃ n) (x : GL n k) :
    ∃ p : parab k e, ∃ w ∈ (KO k n : Set (GL n k)), x = p * w := by sorry
