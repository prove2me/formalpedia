-- Prove2me | Theorems.Thm_MinFracProphet_theorem_2_upper_bound_na
-- name    : MinFracProphet.theorem_2_upper_bound_na
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:35:28.008276+00:00
-- url     : https://prove2.me/theorems/27af19fd-b7be-4c3b-a983-849fa21a88b7
-- title:
--   Proof of Theorem 2 (upper bound), p.13: $\sup_D \mathbb E[\mathrm{ALG}^{\mathrm{NA}}]/\mathbb E[\mathrm{OPT}]=(1+(n-1)\ell^q)^{-1/q}$
-- statement:
--   Let $n\ge1$, $p>1$, $q=-\frac1{p-1}$ and $0<\ell<1$. Over all instances with in-house production (seller $1$ at the constant price $1$, the laws $D_2,\dots,D_n$ arbitrary probability distributions with support in $[\ell,\infty)$, possibly with infinite mean), the worst-case ratio of the non-adaptive algorithm NA is
--   $$
--   \sup_{D}\ \frac{\mathbb E[\mathrm{ALG}^{\mathrm{NA}}(C,p)]}{\mathbb E[\mathrm{OPT}(C,p)]}=\bigl(1+(n-1)\ell^q\bigr)^{-1/q}.
--   $$
--   Since $-1/q=p-1$ and $\ell^q=\ell^{-1/(p-1)}$, the right side is the value $\bigl(1+\frac{n-1}{\ell^{1/(p-1)}}\bigr)^{p-1}$ of (3), so NA certifies the upper bound of Theorem 2.
--
--   **Formalization Note** $\mathbb E[\mathrm{ALG}^{\mathrm{NA}}]$ is the optimal value of (8), computed in $[0,\infty]$, where $0\cdot\infty=0$; $\mathbb E[\mathrm{OPT}]$ is a lower Lebesgue integral. By Lemma 3 this is the paper's ratio $M_q(1,\mathbb E[C])/\mathbb E[M_q(1,C)]$ in (10).
--
--   Differences from the source:
--   - reading: sup_D M_q(1,E[C])/E[M_q(1,C)] = lim_{ε_i→0} n^{−1/q}/E[M_q(1,C)] = n^{−1/q}(M_q(1,ℓ,…,ℓ))^{−1} = (1+(n−1)ℓ^q)^{−1/q}, with infinite means allowed (ℝ ∪ {±∞}, 0·∞ := 0) → sup over in-house instances of NAvalue/EOPT (in ℝ≥0∞) equals (1+(n−1)ℓ^q)^{−1/q}; reason: by Lemma 3 the page’s power-mean ratio is the NA ratio (10); the chain’s middle members say where the supremum is approached (long-shot laws, ε_i → 0) and evaluate it, and the equality of its outer members is the conclusion; the long-shot limit of E[OPT] is the lower-bound milestone
--   - reading: ℓ < 1 (positivity of ℓ not written) → 0 < ℓ < 1; reason: prices are non-negative (§1.2) and (3) divides by ℓ^{1/(p−1)}, so ℓ > 0 is implicit; for ℓ ≤ 0 the formula is undefined
--   - encoding: sellers 1,…,n, seller 1 in-house (P[C_1 = 1] = 1) → sellers Fin n with 0 < n, seller 0 in-house (law dirac 1); reason: Lean convention; n counts the in-house seller and n = 0 has no feasible allocation
--   - encoding: expectations and the ratio E[ALG^π]/E[OPT] in the extended reals → lower Lebesgue integrals (lintegral) of ENNReal.ofReal, ratio in ℝ≥0∞; reason: same values: on an in-house instance 0 < E[OPT] ≤ 1, and E[ALG^π] = ∞ gives the ratio ∞ as in the paper
--   - encoding: 𝒟 = distributions whose support is contained in [ℓ,∞) → probability measures ν on ℝ with ν((−∞,ℓ)) = 0, no moment condition; reason: same class; infinite means stay allowed, as the paper’s proof uses (p.12)
--   - encoding: independent random variables C_i ∼ D_i → the product measure Measure.pi ν on ℝ^n; reason: independence is the product law
-- source:
--   Qin, Vardi, Wierman, Minimization Fractional Prophet Inequalities for Sequential Procurement, author manuscript (INFORMS template, sha256 672fa87c…79125d3), proof of Theorem 2 (upper bound), final display, p.13 (with (10), p.12)

import Mathlib
import Definitions.Def_MinFracProphet_Model

open MeasureTheory

namespace MinFracProphet

/-- **Proof of Theorem 2 (upper bound), final display**, p.13 of J. Qin, S. Vardi, A. Wierman,
*Minimization Fractional Prophet Inequalities for Sequential Procurement*, author manuscript
(sha256 672fa87c…79125d3).

For `n ≥ 1`, `p > 1`, `q = -1/(p-1)` and `0 < ℓ < 1`, the worst case of the non-adaptive
algorithm NA over all instances with in-house production (seller 1 at the constant price `1`,
the other sellers' laws arbitrary on `[ℓ,∞)`) is
`sup_D E[ALG^NA(C,p)] / E[OPT(C,p)] = (1 + (n-1) ℓ^q)^{-1/q}`.

**Formalization Note** By Lemma 3 the page's `M_q(1,E[C]) / E[M_q(1,C)]` is the NA ratio (10);
it is stated here as `NAvalue / EOPT` (R8), with expectations in `ℝ≥0∞`, over all laws on
`[ℓ,∞)` including those with infinite mean (the paper's extended-real convention `0·∞ = 0`, p.12,
is `ℝ≥0∞` multiplication). Sellers are `Fin n`, seller `0` in-house (R2); `ℓ > 0` (R1). -/
theorem theorem_2_upper_bound_na (n : ℕ) (hn : 0 < n) (p : ℝ) (hp : 1 < p) (q : ℝ)
    (hq : q = -1 / (p - 1)) (ℓ : ℝ) (hℓ0 : 0 < ℓ) (hℓ1 : ℓ < 1) :
    (⨆ (ν : Fin n → Measure ℝ) (_ : IsInHouseInstance n ℓ ν), NAvalue p ν / EOPT p ν) =
      ENNReal.ofReal ((1 + ((n : ℝ) - 1) * ℓ ^ q) ^ (-1 / q)) := by sorry

end MinFracProphet
