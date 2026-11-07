-- Prove2me | Theorems.Thm_LDPSelect_lp_value
-- name    : LDPSelect.lp_value
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T15:56:41.291209+00:00
-- url     : https://prove2.me/theorems/fe53d21a-8bc4-4e04-90fb-eed032bc399f
-- title:
--   A.5 — the best shared kernel at thresholds $\ell,h$ loses exactly $\Delta(a)$
-- statement:
--   Let $a>1$, $\mu>0$, $\delta=\frac{(a-1)\mu}{2(a+2)}$, $\ell=\mu-\delta$, $h=\mu+\delta$, and let $Y$ be uniform on $\{0,\mu,2\mu\}$. For a private kernel $Q$ on $\{0,\mu,2\mu\}$ and a threshold $t$ let $G_t(Q)=\sup_\varphi\mathbb E[(Y-t)\varphi(Z)]$.
--
--   1. Over all output spaces and all $a$-locally private $Q$,
--   $$\sup_Q\tfrac12\big(G_\ell(Q)+G_h(Q)\big)=\mathrm{LP}^\star=\begin{cases}\dfrac{(a-1)\mu}{3(a+1)}, & 1<a\le3,\\[2mm] \dfrac{5(a-1)\mu}{12(a+2)}, & a\ge3,\end{cases}$$
--   and the supremum is attained.
--   2. When each threshold receives its own optimal kernel the value is $\tfrac12\big((F_a(Y,\ell)-\ell)+(F_a(Y,h)-h)\big)=\frac{(a-1)(2\mu+\delta)}{6(a+1)}$.
--   3. Their difference is $\Delta(a)$ of Proposition 12.
--
--   This is the exact loss of one kernel forced to serve two capacity states.
--
--   Differences from the source:
--   - reading: LP⋆ as a maximum over ray mixtures c ≥ 0 with Σ_S c_S r_S = 1 → the supremum of ½(G_ℓ(Q) + G_h(Q)) over all a-private kernels Q, as an upper bound and an attaining kernel; reason: A.5 uses LP⋆ as the value of the best shared kernel (∆(a) = min_Q ½(L_ℓ(Q) + L_h(Q)), p.19), and Lemma 22 makes the two equal
--   - encoding: inputs {0, µ, 2µ} → inputs j : Fin 3 standing for jµ; reason: relabelling of a three-point set
--   - encoding: an arbitrary measurable output space → an output type `Z : Type` with a measurable structure; reason: every output space used in the paper lives in `Type`, and the payoff depends on a report only through the acceptance probability it induces
-- source:
--   Chen, Wang, When Does Private Data Collection Need Interaction? Online Selection under Local Differential Privacy, STOC 2027 submission (manuscript sha256 2e2d6157…), A.5, pp.18–19 (pdf pp.19–20)

import Mathlib
import Definitions.Def_LDPSelect_Fa
import Definitions.Def_LDPSelect_TwoState

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LDPSelect

/-- Chen, Wang, *When Does Private Data Collection Need Interaction? Online Selection under Local Differential Privacy*, STOC 2027 submission (manuscript sha256 2e2d6157…), A.5, pp.18–19.

Let `G_t(Q) = sup_φ E[(Y − t) φ(Z)]` with `Y` uniform on `{0, μ, 2μ}`. The supremum over private `Q` of
`½ (G_ℓ(Q) + G_h(Q))` is `(a−1)μ/(3(a+1))` for `a ≤ 3` and `5(a−1)μ/(12(a+2))` for `a ≥ 3`, and it is
attained; the value when each threshold has its own optimal kernel is `(a−1)(2μ+δ)/(6(a+1))`; the
difference is `∆(a)`.

**Formalization Note.** Input `j : Fin 3` is the value `j μ`. The double supremum over `Q` and two
post-processings is written as an upper bound together with attainment, over every output type `Z`.
The paper's LP value `LP⋆` is this quantity written over the rays of Lemma 22. -/
theorem lp_value (a μ : ℝ) (ha : 1 < a) (hμ : 0 < μ) :
    let lpVal : ℝ := if a ≤ 3 then (a - 1) * μ / (3 * (a + 1))
      else 5 * (a - 1) * μ / (12 * (a + 2))
    let val := fun {Z : Type} [MeasurableSpace Z] (Q : Fin 3 → Measure Z) (φ : Z → ℝ) (t : ℝ) =>
      (1 / 3 : ℝ) * ∑ j : Fin 3, (((j : ℕ) : ℝ) * μ - t) * ∫ z, φ z ∂Q j
    (∀ (Z : Type) (_ : MeasurableSpace Z) (Q : Fin 3 → Measure Z) (φ₁ φ₂ : Z → ℝ),
      (∀ j, IsProbabilityMeasure (Q j)) →
      (∀ (j j' : Fin 3) (A : Set Z), MeasurableSet A → Q j A ≤ ENNReal.ofReal a * Q j' A) →
      IsPostProcessing φ₁ → IsPostProcessing φ₂ →
      (1 / 2 : ℝ) * (val Q φ₁ (ell a μ) + val Q φ₂ (high a μ)) ≤ lpVal) ∧
    (∃ (Z : Type) (_ : MeasurableSpace Z) (Q : Fin 3 → Measure Z) (φ₁ φ₂ : Z → ℝ),
      (∀ j, IsProbabilityMeasure (Q j)) ∧
      (∀ (j j' : Fin 3) (A : Set Z), MeasurableSet A → Q j A ≤ ENNReal.ofReal a * Q j' A) ∧
      IsPostProcessing φ₁ ∧ IsPostProcessing φ₂ ∧
      (1 / 2 : ℝ) * (val Q φ₁ (ell a μ) + val Q φ₂ (high a μ)) = lpVal) ∧
    (1 / 2 : ℝ) * ((Fa a (Y μ) (ell a μ) - ell a μ) + (Fa a (Y μ) (high a μ) - high a μ)) =
      (a - 1) * (2 * μ + deltaParam a μ) / (6 * (a + 1)) ∧
    (a - 1) * (2 * μ + deltaParam a μ) / (6 * (a + 1)) - lpVal = gapDelta a μ := by sorry

end LDPSelect
