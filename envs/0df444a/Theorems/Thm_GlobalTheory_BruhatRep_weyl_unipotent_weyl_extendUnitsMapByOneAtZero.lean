-- Prove2me | Theorems.Thm_GlobalTheory_BruhatRep_weyl_unipotent_weyl_extendUnitsMapByOneAtZero
-- name    : GlobalTheory.BruhatRep.weyl_unipotent_weyl_extendUnitsMapByOneAtZero
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T11:02:55.416494+00:00
-- url     : https://prove2.me/theorems/df60f086-6f7f-4868-b58b-c33526655019
-- title:
--   Bruhat Rep: weyl unipotent weyl extend Units Map By One At Zero
-- statement:
--   The Bruhat Rep construction uses the weyl unipotent weyl extend Units Map By One At Zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/Sl2PresentationRelations.lean#L97-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/Sl2PresentationRelations.lean#L97-L103

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

theorem GlobalTheory.BruhatRep.weyl_unipotent_weyl_extendUnitsMapByOneAtZero (htnt : ∀ u : Kˣ, t * n u * t = n (-((u⁻¹ : Kˣ) : K)) * m (-u⁻¹) * t * n (-((u⁻¹ : Kˣ) : K)))
    {u : K} (hu : u ≠ 0) : t * n u * t = n (-u⁻¹) * mx m (-u⁻¹) * t * n (-u⁻¹) := by sorry
