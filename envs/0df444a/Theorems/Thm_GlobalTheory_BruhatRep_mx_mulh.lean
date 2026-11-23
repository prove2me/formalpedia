-- Prove2me | Theorems.Thm_GlobalTheory_BruhatRep_mx_mulh
-- name    : GlobalTheory.BruhatRep.mx_mulh
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:02:08.664279+00:00
-- url     : https://prove2.me/theorems/a70b51b4-85d8-41d4-abe7-55471ef2ba73
-- title:
--   Bruhat Rep: mx mulh
-- statement:
--   The Bruhat Rep construction uses the mx mulh property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/Sl2PresentationRelations.lean#L64-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/Sl2PresentationRelations.lean#L64-L66

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsStableGauss
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_Sl2PresentationRelations
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR GlobalTheory.JR.WeilQuad Matrix MeasureTheory Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.BruhatRep
variable {K : Type} [Field K]
variable {M : Type} [Monoid M]
variable (n : K → M) (m : Kˣ → M) (t : M)

theorem GlobalTheory.BruhatRep.mx_mulh (hm : ∀ a b, m (a * b) = m a * m b) {x y : K} (hx : x ≠ 0) (hy : y ≠ 0) (X : M) :
    X * mx m x * mx m y = X * mx m (x * y) := by sorry
