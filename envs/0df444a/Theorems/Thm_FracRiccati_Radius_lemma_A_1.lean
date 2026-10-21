-- Prove2me | Theorems.Thm_FracRiccati_Radius_lemma_A_1
-- name    : FracRiccati.Radius.lemma_A_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T09:15:22.957172+00:00
-- url     : https://prove2.me/theorems/6378db5c-af28-4e22-b3fe-2e3b4b2d0771
-- title:
--   Lemma A.1 (A.39), p. 25 — Riemann-sum bounds for a symmetric function non-increasing on (0, 1/2]
-- statement:
--   Let $f:(0,1)\to\mathbb R_+$ be non-increasing on $(0,\tfrac12]$, symmetric, i.e. $f(1-x)=f(x)$ for $x\in(0,1)$, and integrable: $\int_0^1f(u)\,du<+\infty$. Then $\inf_{x\in(0,1)}f(x)=f(\tfrac12)$, and for every integer $k\ge1$
--   $$\Big(1-\frac1k\Big)f\Big(\frac12\Big)\le\frac1k\sum_{\ell=1}^{k-1}f\Big(\frac\ell k\Big)\le\int_0^1f(u)\,du-\mathbf 1_{\{k\text{ even}\}}\int_{1/2}^{1/2+1/k}f(u)\,du-\mathbf 1_{\{k\text{ odd}\}}\int_{\frac{k-1}{2k}}^{\frac{k+1}{2k}}f(u)\,du. \qquad (A.39)$$
--
--   The lemma converts the discrete convolution sums $\sum_\ell \ell^{\alpha-1}(k-\ell)^{\alpha-1}$ that arise from the recursion (3.19) into Beta integrals. It is applied in Appendix B to $f_\alpha(x)=(x(1-x))^{\alpha-1}$ for $\alpha\in(0,1]$ and to $\tilde f_\alpha=f_\alpha(\tfrac12)-f_\alpha$ for $\alpha\in[1,2]$.
--
--   **Formalization Note** The page's "hence convex" does not follow from symmetry and monotonicity. The lower inequality follows directly because every summand is at least $f(1/2)$; the upper inequality uses monotonicity and symmetry. No convexity hypothesis is needed. $f$ is a function $\mathbb R\to\mathbb R$ whose hypotheses are imposed on $(0,1)$ only; integrability is `IntegrableOn f (Ioo 0 1)`, and the integrals are interval integrals. The infimum statement is `IsLeast (f '' (0,1)) (f (1/2))`. For $k=1$ all three members are $0$.
-- source:
--   Callegaro, Grasselli, Pagès, Fast Hybrid Schemes for Fractional Riccati Equations (Rough is not so Tough), arXiv:1805.12587v4, p. 25, Lemma A.1, (A.39)

import Mathlib

namespace FracRiccati.Radius

theorem lemma_A_1 (f : ℝ → ℝ)
    (hf_nonneg : ∀ x ∈ Set.Ioo (0 : ℝ) 1, 0 ≤ f x)
    (hf_anti : AntitoneOn f (Set.Ioc (0 : ℝ) (1 / 2)))
    (hf_symm : ∀ x ∈ Set.Ioo (0 : ℝ) 1, f (1 - x) = f x)
    (hf_int : MeasureTheory.IntegrableOn f (Set.Ioo (0 : ℝ) 1)) :
    IsLeast (f '' Set.Ioo (0 : ℝ) 1) (f (1 / 2)) ∧
    ∀ k : ℕ, 1 ≤ k →
      (1 - 1 / (k : ℝ)) * f (1 / 2) ≤ (1 / (k : ℝ)) * ∑ ℓ ∈ Finset.Ico 1 k, f ((ℓ : ℝ) / k) ∧
      (1 / (k : ℝ)) * ∑ ℓ ∈ Finset.Ico 1 k, f ((ℓ : ℝ) / k) ≤
        (∫ u in (0 : ℝ)..1, f u)
          - (if Even k then (∫ u in (1 / 2 : ℝ)..(1 / 2 + 1 / (k : ℝ)), f u) else 0)
          - (if Odd k then (∫ u in ((k : ℝ) - 1) / (2 * k)..((k : ℝ) + 1) / (2 * k), f u)
              else 0) := by sorry

end FracRiccati.Radius
