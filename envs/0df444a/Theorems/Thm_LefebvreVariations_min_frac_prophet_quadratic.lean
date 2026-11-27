-- Prove2me | Theorems.Thm_LefebvreVariations_min_frac_prophet_quadratic
-- name    : LefebvreVariations.min_frac_prophet_quadratic
-- status  : Open
-- author  : @Secousses
-- created : 2026-11-26T22:19:24.951239+00:00
-- url     : https://prove2.me/theorems/d5312070-adc3-4cf1-b69f-dc2235272753
-- title:
--   Lefebvre's variations, No. 252 — on a theme by Qin, Vardi and Wierman: the long-shot law minimizes the expectation of a negative square under a mean constraint
-- statement:
--   Let $0<\ell\le\mu\le u$ and let $\mathcal C$ be the set of probability laws $\nu$ on $\mathbb R$ carried by $[\ell,u]$ with mean $\int c\,d\nu(c)=\mu$. Let $f(c)=-c^2$, and let $D^\star=\frac{u-\mu}{u-\ell}\delta_\ell+\frac{\mu-\ell}{u-\ell}\delta_u$. Then:
--
--   1. every minimizer $\nu^\star$ of $\nu\mapsto\int f\,d\nu$ over $\mathcal C$ satisfies $\nu^\star(\mathbb R\setminus\{\ell,u\})=0$, and if $\ell<u$ then $\nu^\star=D^\star$;
--   2. if $\ell<u$, then $D^\star\in\mathcal C$ and $\int f\,dD^\star\le\int f\,d\nu$ for every $\nu\in\mathcal C$.
--
--   This is Lemma 2 of a paper on minimization fractional prophet inequalities, which the platform lists as open for every strictly concave $f$ on $[\ell,u]$; here $f$ is the strictly concave quadratic $-c^2$, so that minimizing $E[f(C)]$ means maximizing the second moment at fixed mean.
--
--   **Formalization Note** `f := fun c => -(c ^ 2)`, with the class `𝒞`, the law `Dstar` and the two clauses exactly as in the parent (Bochner integrals; for `ℓ = u` the printed probabilities are `0/0`, so the identification with `D⋆` is claimed only for `ℓ < u`).
--
--   **Why this is a variation.** A variation on the open platform problem MinFracProphet.lemma_2 (under a mean constraint, a strictly concave f is minimized in expectation only by the long-shot two-point law on {ℓ, u}), played for the particular strictly concave function f(c) = -c² with the parent's class, law and clauses restated verbatim, not imported. The lemma for every strictly concave f stays open.
--
--   **Attribution.** This statement belongs to *Lefebvre's variations*, a series proposed by Erwan Lefebvre: each variation plays an open problem of the platform at its first non-trivial size, so that it can be settled and then reused to attack the open problem itself.
-- source:
--   Elementary: for C in [l,u], (C-l)(u-C) >= 0 gives E[C^2] <= (l+u) mu - l u, with equality iff C is carried by {l,u}; the two-point law with mean mu is unique. The general lemma is Lemma 2 of Qin, Vardi, Wierman, Minimization Fractional Prophet Inequalities for Sequential Procurement, as quoted on the platform.

import Mathlib

set_option autoImplicit false

open MeasureTheory

namespace LefebvreVariations

/-- The case of the strictly concave function `f(c) = −c²` of `MinFracProphet.lemma_2` (Qin, Vardi, Wierman,
*Minimization Fractional Prophet Inequalities for Sequential Procurement*, Lemma 2): for `0 < ℓ ≤ μ ≤ u`, every law
`ν` carried by `[ℓ, u]` with mean `μ` that minimizes `E_ν[−C²]` (i.e. maximizes the second moment) among such laws
is concentrated on `{ℓ, u}` and, if `ℓ < u`, equals the long-shot law with mass `(u − μ)/(u − ℓ)` at `ℓ` and
`(μ − ℓ)/(u − ℓ)` at `u`; and if `ℓ < u` this law is in the class and attains the minimum.
Source: elementary (`E[C²] ≤ (ℓ + u) μ − ℓ u` since `(C − ℓ)(u − C) ≥ 0`, with equality exactly on `{ℓ, u}`). -/
theorem min_frac_prophet_quadratic (ℓ μ u : ℝ) (hℓ : 0 < ℓ) (hℓμ : ℓ ≤ μ) (hμu : μ ≤ u) :
    let f : ℝ → ℝ := fun c => -(c ^ 2)
    let 𝒞 : Set (Measure ℝ) :=
      {ν | IsProbabilityMeasure ν ∧ ν (Set.Icc ℓ u)ᶜ = 0 ∧ ∫ c, c ∂ν = μ}
    let Dstar : Measure ℝ :=
      ENNReal.ofReal ((u - μ) / (u - ℓ)) • Measure.dirac ℓ +
        ENNReal.ofReal ((μ - ℓ) / (u - ℓ)) • Measure.dirac u
    (∀ νstar ∈ 𝒞, (∀ ν ∈ 𝒞, ∫ c, f c ∂νstar ≤ ∫ c, f c ∂ν) →
        νstar ({ℓ, u} : Set ℝ)ᶜ = 0 ∧ (ℓ < u → νstar = Dstar)) ∧
      (ℓ < u → Dstar ∈ 𝒞 ∧ ∀ ν ∈ 𝒞, ∫ c, f c ∂Dstar ≤ ∫ c, f c ∂ν) := by
  sorry

end LefebvreVariations
