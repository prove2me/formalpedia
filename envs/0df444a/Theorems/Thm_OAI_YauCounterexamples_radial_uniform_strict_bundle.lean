-- Prove2me | Theorems.Thm_OAI_YauCounterexamples_radial_uniform_strict_bundle
-- name    : OAI.YauCounterexamples.radial_uniform_strict_bundle
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T11:45:54.675362+00:00
-- url     : https://prove2.me/theorems/f8841aaf-94b7-46d8-8a8c-518736b6e69b
-- title:
--   OAI.YauCounterexamples.radial_uniform_strict_bundle: intermediate lemma from OpenAI, Smooth counterexamples to Yau's nodal upper bound in dimensions three and four
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.YauCounterexamples.sphere_three` and `OAI.YauCounterexamples.sphere_two_torus_two`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Smooth counterexamples to Yau's nodal upper bound in dimensions three and four*, OpenAI Math Release, September 23, 2026, result family 350, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.YauCounterexamples.radial_uniform_strict_bundle` of [lean/OAI/Geometry/SmoothYau/Geometry/ProfileTraceAdd.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/SmoothYau/Geometry/ProfileTraceAdd.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.YauCounterexamples`, with `open Set Filter Function Metric`, `open scoped Topology`, `open Set Filter Function Metric`, `open scoped Topology ContDiff InnerProductSpace`, `open Filter Set`, `open scoped Topology`, `open scoped InnerProductSpace`):
--
--   ```lean
--   theorem radial_uniform_strict_bundle {X : Type*} {V : X → Type*}
--       [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
--       [∀ x, FiniteDimensional ℝ (V x)] (hd : ∀ x, 3 ≤ Module.finrank ℝ (V x))
--       (a : ∀ x, V x) (H : ∀ x, ProfileForm (V x)) (χ : X → ℝ)
--       (r e : ℕ → ∀ x, V x) (R T : ℕ → ∀ x, V x →L[ℝ] ℝ)
--       (f b f₂ : ℕ → X → ℝ) (B Er : ℕ → ∀ x, ProfileForm (V x))
--       (m α M Hmax δ A K S R₀ Fmax Ce Cr : ℝ)
--       (hm : 0 < m) (hm1 : m ≤ 1) (hα : 0 < α) (hM : 0 ≤ M) (hHmax : 0 ≤ Hmax)
--       (hδ : 0 < δ) (hA : 0 < A) (hK : 0 ≤ K) (hS : 0 ≤ S) (hR₀ : 0 < R₀)
--       (hFmax : 0 ≤ Fmax) (hCe : 0 ≤ Ce) (hCr : 0 ≤ Cr)
--       (hsmall : 9216*K*S*δ^2 ≤ 1)
--       (ha0 : ∀ x, α ≤ ‖a x‖) (haM : ∀ x, ‖a x‖ ≤ M)
--       (hHH : ∀ x, ‖H x‖ ≤ Hmax) (hAa : ∀ x, A ≤ 2*‖a x‖)
--       (hmargin : ∀ x w, ‖w‖ = 1 → inner ℝ (a x) w = 0 → m ≤ profileTrace (H x) (a x) w)
--       (hχ : ∀ x, 0 ≤ χ x ∧ χ x ≤ 1)
--       (hf : ∀ N x, 0 ≤ f N x ∧ f N x ≤ Fmax)
--       (hb : ∀ N x, f N x/R₀ ≤ b N x) (hfS : ∀ N x, (f N x)^2 ≤ S*b N x)
--       (hf₂ : ∀ N x, |f₂ N x| ≤ K)
--       (hr : ∀ N x v, inner ℝ (r N x) v = R N x v)
--       (hRa : ∀ N x, R N x (a x) = 0) (hTa : ∀ N x, T N x (a x) = 0)
--       (hrn : ∀ N x, ‖r N x‖ ≤ 2)
--       (hco : ∀ N x v, inner ℝ (a x) v = 0 →
--         ‖v‖/2 ≤ Real.sqrt ((R N x v)^2+(T N x v)^2))
--       (hB : ∀ N x u v, B N x u v = f₂ N x*R N x u*R N x v+b N x*T N x u*T N x v)
--       (he : ∀ᶠ N : ℕ in atTop, ∀ x, ‖e N x‖ ≤ Ce/(N:ℝ))
--       (hEr : ∀ᶠ N : ℕ in atTop, ∀ x, ‖Er N x‖ ≤
--         Cr*(χ x*f N x+Real.sqrt (χ x*f N x)+(N:ℝ)⁻¹)) :
--       ∀ᶠ N : ℕ in atTop, ∀ x,
--         profileStrict (H x+((N:ℝ)*δ*A*χ x) • B N x+Er N x)
--           (a x+(δ*A*χ x*f N x) • r N x+e N x) ∧
--         a x+(δ*A*χ x*f N x) • r N x+e N x ≠ 0
--   ```
--
--   **Definitions.** The statement is written with `OAI.YauCounterexamples.ProfileForm` (definitions bundle `OAIQ070A002` of this split); `OAI.YauCounterexamples.profileStrict` and `OAI.YauCounterexamples.profileTrace` (definitions bundle `OAIQ070A007` of this split).
--
--   **Used by.** The proof of `OAI.YauCounterexamples.actual_radialCorrugation_strict_shift` of this split imports it.
-- source:
--   OpenAI, Smooth counterexamples to Yau's nodal upper bound in dimensions three and four, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 350; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/Smooth-counterexamples-to-Yaus-nodal-upper-bound-in-dimensions-three-and-four-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/SmoothYau/Geometry/ProfileTraceAdd.lean (declaration OAI.YauCounterexamples.radial_uniform_strict_bundle)

import Mathlib
import Definitions.Def_OAIQ070A007

section

attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples

open Set Filter Function Metric
open scoped Topology
open Set Filter Function Metric
open scoped Topology ContDiff InnerProductSpace
open Filter Set
open scoped Topology
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem radial_uniform_strict_bundle {X : Type*} {V : X → Type*}
    [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
    [∀ x, FiniteDimensional ℝ (V x)] (hd : ∀ x, 3 ≤ Module.finrank ℝ (V x))
    (a : ∀ x, V x) (H : ∀ x, ProfileForm (V x)) (χ : X → ℝ)
    (r e : ℕ → ∀ x, V x) (R T : ℕ → ∀ x, V x →L[ℝ] ℝ)
    (f b f₂ : ℕ → X → ℝ) (B Er : ℕ → ∀ x, ProfileForm (V x))
    (m α M Hmax δ A K S R₀ Fmax Ce Cr : ℝ)
    (hm : 0 < m) (hm1 : m ≤ 1) (hα : 0 < α) (hM : 0 ≤ M) (hHmax : 0 ≤ Hmax)
    (hδ : 0 < δ) (hA : 0 < A) (hK : 0 ≤ K) (hS : 0 ≤ S) (hR₀ : 0 < R₀)
    (hFmax : 0 ≤ Fmax) (hCe : 0 ≤ Ce) (hCr : 0 ≤ Cr)
    (hsmall : 9216*K*S*δ^2 ≤ 1)
    (ha0 : ∀ x, α ≤ ‖a x‖) (haM : ∀ x, ‖a x‖ ≤ M)
    (hHH : ∀ x, ‖H x‖ ≤ Hmax) (hAa : ∀ x, A ≤ 2*‖a x‖)
    (hmargin : ∀ x w, ‖w‖ = 1 → inner ℝ (a x) w = 0 → m ≤ profileTrace (H x) (a x) w)
    (hχ : ∀ x, 0 ≤ χ x ∧ χ x ≤ 1)
    (hf : ∀ N x, 0 ≤ f N x ∧ f N x ≤ Fmax)
    (hb : ∀ N x, f N x/R₀ ≤ b N x) (hfS : ∀ N x, (f N x)^2 ≤ S*b N x)
    (hf₂ : ∀ N x, |f₂ N x| ≤ K)
    (hr : ∀ N x v, inner ℝ (r N x) v = R N x v)
    (hRa : ∀ N x, R N x (a x) = 0) (hTa : ∀ N x, T N x (a x) = 0)
    (hrn : ∀ N x, ‖r N x‖ ≤ 2)
    (hco : ∀ N x v, inner ℝ (a x) v = 0 →
      ‖v‖/2 ≤ Real.sqrt ((R N x v)^2+(T N x v)^2))
    (hB : ∀ N x u v, B N x u v = f₂ N x*R N x u*R N x v+b N x*T N x u*T N x v)
    (he : ∀ᶠ N : ℕ in atTop, ∀ x, ‖e N x‖ ≤ Ce/(N:ℝ))
    (hEr : ∀ᶠ N : ℕ in atTop, ∀ x, ‖Er N x‖ ≤
      Cr*(χ x*f N x+Real.sqrt (χ x*f N x)+(N:ℝ)⁻¹)) :
    ∀ᶠ N : ℕ in atTop, ∀ x,
      profileStrict (H x+((N:ℝ)*δ*A*χ x) • B N x+Er N x)
        (a x+(δ*A*χ x*f N x) • r N x+e N x) ∧
      a x+(δ*A*χ x*f N x) • r N x+e N x ≠ 0 := by
  sorry

end YauCounterexamples
end

end OAI
end
