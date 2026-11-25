-- Prove2me | Theorems.Thm_GlobalTheory_CycFr_constantCoeff_algHom
-- name    : GlobalTheory.CycFr.constantCoeff_algHom
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T02:01:46.994011+00:00
-- url     : https://prove2.me/theorems/20c654ee-3154-43d3-baa9-966023a7db7e
-- title:
--   Cyc Fr: constant Coeff alg Hom
-- statement:
--   The Cyc Fr construction uses the constant Coeff alg Hom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/OneAddXMulDerivativeBin.lean#L51-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/OneAddXMulDerivativeBin.lean#L51-L59

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_OneAddXMulDerivativeBin
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PowerSeries
open GlobalTheory GlobalTheory.CycFr
open PowerSeries

theorem GlobalTheory.CycFr.constantCoeff_algHom {O : Type} [CommRing O] (f : O⟦X⟧ →ₐ[O] O⟦X⟧)
    (hf : (X : O⟦X⟧) ∣ f X) (a : O⟦X⟧) : constantCoeff (f a) = constantCoeff a := by sorry
