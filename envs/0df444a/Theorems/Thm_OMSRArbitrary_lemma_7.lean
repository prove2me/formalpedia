-- Prove2me | Theorems.Thm_OMSRArbitrary_lemma_7
-- name    : OMSRArbitrary.lemma_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:36:54.283721+00:00
-- url     : https://prove2.me/theorems/cc7f7bcc-868b-45c3-8c58-4a85e4e8646c
-- title:
--   Lemma 7 — $\int_0^1\gamma\ge\alpha(g)$ and $\int_0^1\gamma_\Lambda\ge\alpha_\Lambda(g,c)$, both tight
-- statement:
--   Let $g:[0,1]\to[0,1]$ be continuous and nondecreasing with $g(1)<1$, $c$ integrable with $0\le c\le g$, and $\Lambda\in[1,\infty]$.
--
--   **Lemma 7.** For every $\pi\ge0$,
--   $$\int_0^1\gamma(x,\pi)\,dx\ \ge\ \alpha(g)\qquad\text{and}\qquad\int_0^1\gamma_\Lambda(x,\pi)\,dx\ \ge\ \alpha_\Lambda(g,c).$$
--   Both bounds are tight: $\alpha(g)$ and $\alpha_\Lambda(g,c)$ are the infima of the two integrals over $\pi\ge0$.
--
--   This is the analytic half of the proof of Theorems 3 and 4: it turns the per-arrival targets into the closed-form guarantees (3) and (4).
--
--   **Formalization Note** $\Lambda$ enters through $\rho=1/\Lambda\in[0,1]$; tightness is stated as "greatest lower bound".
--
--   Differences from the source:
--   - encoding: g : [0,1] → [0,1] continuous and nondecreasing with g(1) < 1 → g : ℝ → ℝ with ContinuousOn, MonotoneOn and MapsTo on [0,1] and g 1 < 1; reason: only the values of g on [0,1] enter, since seeds lie in [0,1]
--   - encoding: an integrable tradeoff function c : [0,1] → [0,1] with 0 ≤ c ≤ g → c : ℝ → ℝ, IntegrableOn c [0,1], 0 ≤ c x ≤ g x for x ∈ [0,1]; reason: c ≤ g ≤ 1 gives values in [0,1]; values outside [0,1] never enter
--   - encoding: Λ ∈ [1, ∞]; σ_Λ = σ/Λ → ρ = 1/Λ ∈ [0,1]; σ_Λ = ρ σ; reason: ρ = 0 is Λ = ∞ and ρ = 1 is Λ = 1
--   - encoding: α(g) and α_Λ(g, c) are the infima of the two integrals over π ≥ 0 → IsGLB of {∫₀¹ γ(x, π) dx : π ≥ 0} and of {∫₀¹ γ_Λ(x, π) dx : π ≥ 0}; reason: the definition of the infimum
--   - encoding: min over y ∈ [0,1] in (3) and (4) → infimum over the subtype [0,1]; reason: the minimum is attained, so it equals the infimum
-- source:
--   Udwani, Online Matching with Arbitrary Stochastic Rewards, arXiv:2611.03598, Lemma 7, p.15 (proof in App. E, pp.36–37)

import Mathlib
import Definitions.Def_OMSRArbitrary_Targets

open MeasureTheory
noncomputable section

namespace OMSRArbitrary

/-- **Lemma 7** (arXiv:2611.03598, §3.1, p.15; proof in App. E, pp.36–37): for every `π ≥ 0`,
`∫₀¹ γ(x, π) dx ≥ α(g)` and `∫₀¹ γ_Λ(x, π) dx ≥ α_Λ(g, c)`. Both bounds are tight: `α(g)` and
`α_Λ(g, c)` are the infima of the two integrals over `π ≥ 0`.

Clauses 1–2 are the two bounds; clauses 3–4 are the tightness statements, as greatest lower
bounds of `{∫₀¹ γ(x, π) dx : π ≥ 0}` and `{∫₀¹ γ_Λ(x, π) dx : π ≥ 0}`.

**Formalization Note.** `Λ ∈ [1, ∞]` is written `ρ = 1/Λ ∈ [0,1]`; `g` and the tradeoff
function `c` satisfy the paper's hypotheses on `[0,1]`. -/
theorem lemma_7 (g : ℝ → ℝ) (hg_cont : ContinuousOn g (Set.Icc 0 1))
    (hg_mono : MonotoneOn g (Set.Icc 0 1))
    (hg_maps : Set.MapsTo g (Set.Icc 0 1) (Set.Icc 0 1)) (hg_one : g 1 < 1)
    (c : ℝ → ℝ) (hc_int : IntegrableOn c (Set.Icc 0 1))
    (hc_nonneg : ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 ≤ c x) (hc_le : ∀ x ∈ Set.Icc (0 : ℝ) 1, c x ≤ g x)
    (ρ : ℝ) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) :
    (∀ π : ℝ, 0 ≤ π → alpha g ≤ ∫ x in (0 : ℝ)..1, gamma g x π) ∧
    (∀ π : ℝ, 0 ≤ π → alphaW g c ρ ≤ ∫ x in (0 : ℝ)..1, gammaW g c ρ x π) ∧
    IsGLB {I : ℝ | ∃ π : ℝ, 0 ≤ π ∧ I = ∫ x in (0 : ℝ)..1, gamma g x π} (alpha g) ∧
    IsGLB {I : ℝ | ∃ π : ℝ, 0 ≤ π ∧ I = ∫ x in (0 : ℝ)..1, gammaW g c ρ x π}
      (alphaW g c ρ) := by sorry

end OMSRArbitrary
