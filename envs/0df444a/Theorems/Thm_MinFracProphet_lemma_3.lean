-- Prove2me | Theorems.Thm_MinFracProphet_lemma_3
-- name    : MinFracProphet.lemma_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:35:34.473739+00:00
-- url     : https://prove2.me/theorems/1935f116-f25c-4581-8dc7-ca76950098f7
-- title:
--   Lemma 3: the ratio of the non-adaptive algorithm is $M_q(\mathbb E[C])/\mathbb E[M_q(C)]$
-- statement:
--   Fix $p>1$, let $q=-\frac1{p-1}$, let $0<\ell\le u<\infty$ and $n\ge1$, and let $C=(C_1,\dots,C_n)$ have independent coordinates, each with a distribution carried by $[\ell,u]$. Let NA be the non-adaptive algorithm that buys a minimizer of (8). Then
--   $$
--   \frac{\mathbb E[\mathrm{ALG}^{\mathrm{NA}}(C,p)]}{\mathbb E[\mathrm{OPT}(C,p)]}=\frac{M_q(\mathbb E[C])}{\mathbb E[M_q(C)]},
--   $$
--   where $M_q$ is the power mean and $\mathbb E[C]=(\mathbb E[C_1],\dots,\mathbb E[C_n])$.
--
--   This identity reduces the analysis of NA to comparing a power mean of expectations with the expectation of a power mean, which is where Lemma 2 enters.
--
--   **Formalization Note** $\mathbb E[\mathrm{ALG}^{\mathrm{NA}}]$ is the optimal value of (8), and the left side is computed in $[0,\infty]$; the right side is a real number (Bochner integrals of bounded functions), embedded by `ENNReal.ofReal`. Both sides are finite and positive here.
--
--   Differences from the source:
--   - encoding: sellers 1,…,n → sellers Fin n with 0 < n; reason: Lean convention, an index shift; n = 0 has no feasible allocation
--   - encoding: independent random variables C_i ∼ D_i → the product measure Measure.pi ν on ℝ^n; reason: independence is the product law
--   - encoding: E[ALG^NA(C,p)], the expected cost of NA → NAvalue p ν, the optimal value of (8) in ℝ≥0∞; reason: NA buys a minimizer of (8), so its expected cost is that value
--   - encoding: the ratio of expectations → left side in ℝ≥0∞ (lintegral), right side ENNReal.ofReal of a real ratio of Bochner integrals; reason: all quantities are finite and positive for laws carried by [ℓ,u], so both encodings give the same number
--   - encoding: distribution supported on [ℓ,u] → probability measure with ν_i([ℓ,u]ᶜ) = 0; reason: Lean convention; same laws
-- source:
--   Qin, Vardi, Wierman, Minimization Fractional Prophet Inequalities for Sequential Procurement, author manuscript (INFORMS template, sha256 672fa87c…79125d3), Lemma 3, p.12 (restated p.21)

import Mathlib
import Definitions.Def_MinFracProphet_Model

open MeasureTheory

namespace MinFracProphet

/-- **Lemma 3**, p.12 of J. Qin, S. Vardi, A. Wierman, *Minimization Fractional Prophet
Inequalities for Sequential Procurement*, author manuscript (sha256 672fa87c…79125d3).

Fix `p > 1` and `q = -1/(p-1)`, let `0 < ℓ ≤ u < ∞`, and let `C = (C_1, …, C_n)` have independent
coordinates `C_i ∼ ν_i`, each law carried by `[ℓ,u]`. Then the competitive ratio of the
non-adaptive algorithm NA is the power-mean ratio
`E[ALG^NA(C,p)] / E[OPT(C,p)] = M_q(E[C]) / E[M_q(C)]`.

**Formalization Note** `E[ALG^NA(C,p)]` is the optimal value of (8), `NAvalue p ν` (NA buys a
minimizer of (8)). The left side is computed in `ℝ≥0∞` (`lintegral`), the right side in `ℝ`
(Bochner integrals of the bounded functions `c ↦ c` and `c ↦ M_q(c)`); both sides are finite and
positive here. Sellers are `Fin n` with `0 < n` (R2); "supported on `[ℓ,u]`" is
`ν_i([ℓ,u]ᶜ) = 0`. -/
theorem lemma_3 (n : ℕ) (hn : 0 < n) (p : ℝ) (hp : 1 < p) (q : ℝ) (hq : q = -1 / (p - 1))
    (ℓ u : ℝ) (hℓ : 0 < ℓ) (hℓu : ℓ ≤ u) (ν : Fin n → Measure ℝ)
    (hprob : ∀ i, IsProbabilityMeasure (ν i)) (hsupp : ∀ i, ν i (Set.Icc ℓ u)ᶜ = 0) :
    NAvalue p ν / EOPT p ν =
      ENNReal.ofReal (powerMean q (fun i => ∫ c, c ∂(ν i)) /
        ∫ c, powerMean q c ∂(Measure.pi ν)) := by sorry

end MinFracProphet
