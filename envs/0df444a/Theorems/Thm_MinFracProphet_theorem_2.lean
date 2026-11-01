-- Prove2me | Theorems.Thm_MinFracProphet_theorem_2
-- name    : MinFracProphet.theorem_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:35:30.986699+00:00
-- url     : https://prove2.me/theorems/6312d53f-87bf-41f4-bb05-ea5970707b58
-- title:
--   Theorem 2: with in-house production, $\mathrm{CR}_{\text{in-house}}(F,n)=\bigl(1+\frac{n-1}{\ell^{1/(p-1)}}\bigr)^{p-1}$
-- statement:
--   Fix $p>1$ and $0<\ell<1$, let $\mathcal D$ be the set of all probability distributions whose support is contained in $[\ell,\infty)$, and let $F=(\mathcal D,p)$. A buyer procures one unit from $n\ge1$ sellers in sequence, the first of which is in-house production at the constant price $1$, the others having independent prices $C_i\sim D_i\in\mathcal D$; buying $x_i$ from seller $i$ costs $C_ix_i^p$. Then the competitive ratio of the best causal policy against the prophet is
--   $$
--   \mathrm{CR}_{\text{in-house}}(F,n)=\inf_{\pi}\ \sup_{D_2,\dots,D_n\in\mathcal D}\frac{\mathbb E[\mathrm{ALG}^\pi(C,p)]}{\mathbb E[\mathrm{OPT}(C,p)]}=\Bigl(1+\frac{n-1}{\ell^{1/(p-1)}}\Bigr)^{p-1}.\tag{3}
--   $$
--
--   The value is finite for every $\ell>0$, although the prices may be arbitrarily large and even have infinite mean: in-house production insures the buyer against price spikes. Without it the ratio grows with the upper end of the price range (Theorem 3 of the paper).
--
--   **Formalization Note** The infimum ranges over all measurable non-anticipative policies on $\mathbb R^n$, and the supremum over all probability measures on $[\ell,\infty)$, with no moment condition. Expectations are lower Lebesgue integrals and the ratio is computed in $[0,\infty]$. Sellers are `Fin n`, with seller `0` in-house.
--
--   Differences from the source:
--   - reading: ℓ < 1 (positivity of ℓ not written) → 0 < ℓ < 1; reason: prices are non-negative (§1.2) and (3) divides by ℓ^{1/(p−1)}, so ℓ > 0 is implicit; for ℓ ≤ 0 the formula is undefined
--   - encoding: sellers 1,…,n, seller 1 in-house (P[C_1 = 1] = 1) → sellers Fin n with 0 < n, seller 0 in-house (law dirac 1); reason: Lean convention; n counts the in-house seller and n = 0 has no feasible allocation
--   - encoding: policy π = (π_1,…,π_n), π_i : 𝒞_1 × ⋯ × 𝒞_i → [0,1] with Σ x_i = 1 → measurable maps x i : ℝ^n → [0,1] depending only on c_0,…,c_i, with Σ_i x i c = 1 for every c ∈ ℝ^n; reason: a policy on the supports extends to ℝ^n (clamp the prices into the supports) with the same cost on every instance, so the infimum is unchanged; measurability is the standing convention under which E[ALG^π] is defined
--   - encoding: expectations and the ratio E[ALG^π]/E[OPT] in the extended reals → lower Lebesgue integrals (lintegral) of ENNReal.ofReal, ratio in ℝ≥0∞; reason: same values: on an in-house instance 0 < E[OPT] ≤ 1, and E[ALG^π] = ∞ gives the ratio ∞ as in the paper
--   - encoding: 𝒟 = distributions whose support is contained in [ℓ,∞) → probability measures ν on ℝ with ν((−∞,ℓ)) = 0, no moment condition; reason: same class; infinite means stay allowed, as the paper’s proof uses (p.12)
--   - encoding: independent random variables C_i ∼ D_i → the product measure Measure.pi ν on ℝ^n; reason: independence is the product law
-- source:
--   Qin, Vardi, Wierman, Minimization Fractional Prophet Inequalities for Sequential Procurement, author manuscript (INFORMS template, sha256 672fa87c…79125d3), Theorem 2, p.11 (first stated p.4), eq. (3); model §1.2, pp.3–4

import Mathlib
import Definitions.Def_MinFracProphet_Model

namespace MinFracProphet

/-- **Theorem 2**, p.11 (first stated p.4) of J. Qin, S. Vardi, A. Wierman, *Minimization
Fractional Prophet Inequalities for Sequential Procurement*, author manuscript
(sha256 672fa87c…79125d3).

Fix `p > 1`, `0 < ℓ < 1` and `n ≥ 1` sellers, the first of which is in-house production at the
constant price `1`, and let `𝒟` be the set of all distributions with support in `[ℓ,∞)`. Then
the competitive ratio with in-house production is
`CR_in-house(F, n) = (1 + (n-1)/ℓ^{1/(p-1)})^{p-1}`  (3).

**Formalization Note** `CRinHouse n p ℓ` is `inf_π sup_{D_2,…,D_n ∈ 𝒟} E[ALG^π(C,p)]/E[OPT(C,p)]`
over all measurable non-anticipative policies on `ℝ^n` (R3) and all probability laws on `[ℓ,∞)`
(unbounded, infinite means allowed; R5), computed in `ℝ≥0∞` with lower Lebesgue integrals (R4).
Sellers are `Fin n`, seller `0` in-house (R2). The paper writes only `ℓ < 1`; `ℓ > 0` is implicit
in the nonnegative prices and in the division by `ℓ^{1/(p-1)}` (R1). -/
theorem theorem_2 (n : ℕ) (hn : 0 < n) (p : ℝ) (hp : 1 < p) (ℓ : ℝ) (hℓ0 : 0 < ℓ)
    (hℓ1 : ℓ < 1) :
    CRinHouse n p ℓ =
      ENNReal.ofReal ((1 + ((n : ℝ) - 1) / ℓ ^ (1 / (p - 1))) ^ (p - 1)) := by sorry

end MinFracProphet
