-- Prove2me | Theorems.Thm_GlobalTheory_BruhatRep_mx_n
-- name    : GlobalTheory.BruhatRep.mx_n
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:02:04.060803+00:00
-- url     : https://prove2.me/theorems/3f30c90e-ac3c-4394-9635-49b868698c8c
-- title:
--   Bruhat Rep: mx n
-- statement:
--   The Bruhat Rep construction uses the mx n property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/Sl2PresentationRelations.lean#L68-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/Sl2PresentationRelations.lean#L68-L70

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

theorem GlobalTheory.BruhatRep.mx_n (hmn : ∀ s z, m s * n z = n ((s : K) ^ 2 * z) * m s) {x : K} (hx : x ≠ 0) (z : K) :
    mx m x * n z = n (x ^ 2 * z) * mx m x := by sorry
