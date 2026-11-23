-- Prove2me | Theorems.Thm_GlobalTheory_ae_exists_smul_mem_of_surjective
-- name    : GlobalTheory.ae_exists_smul_mem_of_surjective
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:50:29.062953+00:00
-- url     : https://prove2.me/theorems/38781f6d-3e51-4b74-ad5d-473827cf20fa
-- title:
--   Global Theory: ae exists smul mem of surjective
-- statement:
--   The Global Theory construction uses the ae exists smul mem of surjective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/EncardSmulMemLeEncardSmulInterNonempty.lean#L328-L333
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/EncardSmulMemLeEncardSmulInterNonempty.lean#L328-L333

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EncardSmulMemLeEncardSmulInterNonempty
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Set
open scoped ENNReal Pointwise
open GlobalTheory
variable {G H X : Type*} [Group G] [Group H] [MulAction G X] [MulAction H X] [MeasurableSpace X]
  {μ : Measure X} {B D D' : Set X} {φ : G →* H}

theorem GlobalTheory.ae_exists_smul_mem_of_surjective (hφ : Function.Surjective φ)
    (hφs : ∀ (g : G) (x : X), φ g • x = g • x) (hD : IsFundamentalDomain H D μ) :
    ∀ᵐ x ∂μ, ∃ g : G, g • x ∈ D := by sorry
