-- Prove2me | Theorems.Thm_GlobalTheory_BruhatRep_four_eq
-- name    : GlobalTheory.BruhatRep.four_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:02:21.343187+00:00
-- url     : https://prove2.me/theorems/34a20d0e-bde0-4efd-9fe2-dd0419d3ba9a
-- title:
--   Bruhat Rep: four eq
-- statement:
--   The Bruhat Rep construction uses the four eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/Sl2PresentationRelations.lean#L109-L110
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/Sl2PresentationRelations.lean#L109-L110

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

theorem GlobalTheory.BruhatRep.four_eq {a a' b b' c c' : K} (ha : a = a') (hb : b = b') (hc : c = c') :
    n a * mx m b * t * n c = n a' * mx m b' * t * n c' := by sorry
