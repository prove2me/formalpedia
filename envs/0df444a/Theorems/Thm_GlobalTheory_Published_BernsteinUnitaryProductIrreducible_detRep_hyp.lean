-- Prove2me | Theorems.Thm_GlobalTheory_Published_BernsteinUnitaryProductIrreducible_detRep_hyp
-- name    : GlobalTheory.Published.BernsteinUnitaryProductIrreducible.detRep_hyp
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:16:01.830521+00:00
-- url     : https://prove2.me/theorems/3207281d-1746-4d26-b9ac-37e3ed6c24f5
-- title:
--   Bernstein Unitary Product Irreducible: det Rep hyp
-- statement:
--   The Bernstein Unitary Product Irreducible construction uses the det Rep hyp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/TwistedTraceFormula/BernsteinUnitaryProductIrreducible.lean#L31-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/TwistedTraceFormula/BernsteinUnitaryProductIrreducible.lean#L31-L35

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_BernsteinUnitaryProductIrreducible
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SmGL
open GlobalTheory GlobalTheory.Published
open GlobalTheory.Published.BernsteinUnitaryProductIrreducible
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

theorem GlobalTheory.Published.BernsteinUnitaryProductIrreducible.detRep_hyp (t : ℕ) {χ : kˣ →* ℂˣ} (hs : IsSmoothChar χ) (hu : IsUnitaryChar χ) :
    IsSmooth (detRep (Fin t) χ) ∧ (detRep (Fin t) χ).IsIrreducible ∧
      IsUnitarisable (detRep (Fin t) χ) := by sorry
