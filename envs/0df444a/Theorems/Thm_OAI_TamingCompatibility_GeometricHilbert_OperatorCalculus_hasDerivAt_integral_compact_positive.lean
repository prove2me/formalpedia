-- Prove2me | Theorems.Thm_OAI_TamingCompatibility_GeometricHilbert_OperatorCalculus_hasDerivAt_integral_compact_positive
-- name    : OAI.TamingCompatibility.GeometricHilbert.OperatorCalculus.hasDerivAt_integral_compact_positive
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T22:48:55.916986+00:00
-- url     : https://prove2.me/theorems/5638c557-cdb6-4472-b861-e68ae1ebc190
-- title:
--   OAI.TamingCompatibility.GeometricHilbert.OperatorCalculus.hasDerivAt_integral_compact_positive: intermediate lemma from OpenAI, Taming implies compatibility on four-manifolds
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.TamingCompatibility.taming_implies_compatibility`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Taming implies compatibility on four-manifolds*, OpenAI Math Release, October 6, 2026, result family 342, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.TamingCompatibility.GeometricHilbert.OperatorCalculus.hasDerivAt_integral_compact_positive` of [lean/OAI/Geometry/TamingCompatibility/Hodge/HodgeCompactTimeIntegral.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/TamingCompatibility/Hodge/HodgeCompactTimeIntegral.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.TamingCompatibility.GeometricHilbert.OperatorCalculus`, with `open _root_.MeasureTheory Set Filter`, `open scoped Topology`):
--
--   ```lean
--   lemma hasDerivAt_integral_compact_positive (F F' : ℝ → V → ℝ)
--       (K : Set V) (hK : IsCompact K)
--       (hF : ∀ t, 0 < t → Continuous (F t))
--       (hF' : ContinuousOn (fun p : ℝ × V => F' p.1 p.2) (Ioi 0 ×ˢ univ))
--       (hsupp : ∀ t, 0 < t → Function.support (F t) ⊆ K)
--       (hsupp' : ∀ t, 0 < t → Function.support (F' t) ⊆ K)
--       (hd : ∀ t, 0 < t → ∀ x, HasDerivAt (fun s => F s x) (F' t x) t)
--       {t : ℝ} (ht : 0 < t) :
--       HasDerivAt (fun s => ∫ x, F s x ∂μ) (∫ x, F' t x ∂μ) t
--   ```
--
--   **Used by.** The proof of `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.actual_cutoff_time_integral` of this split imports it.
-- source:
--   OpenAI, Taming implies compatibility on four-manifolds, OpenAI Math Release, October 6, 2026, https://github.com/openai/math (result family 342; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Taming-implies-compatibility-on-four-manifolds-October-6-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/TamingCompatibility/Hodge/HodgeCompactTimeIntegral.lean (declaration OAI.TamingCompatibility.GeometricHilbert.OperatorCalculus.hasDerivAt_integral_compact_positive)

import Mathlib

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.OperatorCalculus
open _root_.MeasureTheory Set Filter
open scoped Topology
variable {V : Type*} [TopologicalSpace V] [T2Space V]
  [MeasurableSpace V] [BorelSpace V] (μ : Measure V) [IsFiniteMeasureOnCompacts μ]

lemma hasDerivAt_integral_compact_positive (F F' : ℝ → V → ℝ)
    (K : Set V) (hK : IsCompact K)
    (hF : ∀ t, 0 < t → Continuous (F t))
    (hF' : ContinuousOn (fun p : ℝ × V => F' p.1 p.2) (Ioi 0 ×ˢ univ))
    (hsupp : ∀ t, 0 < t → Function.support (F t) ⊆ K)
    (hsupp' : ∀ t, 0 < t → Function.support (F' t) ⊆ K)
    (hd : ∀ t, 0 < t → ∀ x, HasDerivAt (fun s => F s x) (F' t x) t)
    {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s => ∫ x, F s x ∂μ) (∫ x, F' t x ∂μ) t := by
  sorry

end TamingCompatibility.GeometricHilbert.OperatorCalculus

end
end

end

end OAI
end
