-- Prove2me | Theorems.Thm_GlobalTheory_QuadFibre_fibOf_ne
-- name    : GlobalTheory.QuadFibre.fibOf_ne
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:33:09.366589+00:00
-- url     : https://prove2.me/theorems/75a8ba0d-1a7c-48da-a634-9b5c7ae942a5
-- title:
--   Quad Fibre: fib Of ne
-- statement:
--   The Quad Fibre construction uses the fib Of ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/FibOfZero.lean#L27-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/FibOfZero.lean#L27-L31

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GeneralLinearActions_GenusMassVolumes
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_FibOfZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.QuadFibre
open MeasureTheory
open scoped Pointwise

theorem GlobalTheory.QuadFibre.fibOf_ne {K V : Type} [NormedField K] [MeasurableSpace K] [AddCommGroup V] [Module K V]
    [MeasurableSpace V] (μ : Measure V) (ν : Measure K) (q : V → K) (U : Set K) (s : K → K)
    {t : K} (ht : t ≠ 0) : fibOf μ ν q U s t =
      (ν (t • U))⁻¹ • Measure.map (fun x => s (t / q x) • x) (μ.restrict (q ⁻¹' (t • U))) := by sorry
