-- Prove2me | Theorems.Thm_OptimalRLS_Upper_proposition_1_v
-- name    : OptimalRLS.Upper.proposition_1_v
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T19:25:53.318858+00:00
-- url     : https://prove2.me/theorems/a3987a62-a236-4c17-9c10-00d250e58c62
-- title:
--   Proposition 1 v), (26)–(28), p. 12 — the RLS problem (18) has a unique solution, (T_x + λ) f_z^λ = g_z
-- statement:
--   Assume Hypothesis 1. Let $\ell\ge1$, $\mathbf z=((x_1,y_1),\dots,(x_\ell,y_\ell))\in Z^\ell$ and $\lambda>0$. The regularized empirical risk
--   $$\frac1\ell\sum_{i=1}^\ell\|f(x_i)-y_i\|_Y^2+\lambda\|f\|_{\mathcal H}^2$$
--   has a unique minimizer $f_{\mathbf z}^\lambda\in\mathcal H$, and $f_{\mathbf z}^\lambda=(T_{\mathbf x}+\lambda)^{-1}g_{\mathbf z}$, where
--   $$T_{\mathbf x}=\frac1\ell\sum_{i=1}^\ell K_{x_i}K_{x_i}^*,\qquad g_{\mathbf z}=\frac1\ell\sum_{i=1}^\ell K_{x_i}y_i.$$
--   Equivalently, since $K_x^*f=f(x)$,
--   $$\frac1\ell\sum_{i=1}^\ell K_{x_i}\big(f_{\mathbf z}^\lambda(x_i)\big)+\lambda f_{\mathbf z}^\lambda=\frac1\ell\sum_{i=1}^\ell K_{x_i}y_i.$$
--
--   This is the representer form of the RLS estimator; it shows that the estimator of Theorem 1 is well defined.
--
--   **Formalization Note** The statement records the normal equation $(T_{\mathbf x}+\lambda)f_{\mathbf z}^\lambda=g_{\mathbf z}$, equivalent to (26). Hypothesis 2 is not used by this item (no distribution appears) and is not assumed; the training set has $\ell\ge1$ points.
-- source:
--   Caponnetto & De Vito, Found. Comput. Math. 7 (2007), authors' copy, Proposition 1 v), (26)–(28), p. 12; (18), p. 10

import Mathlib
import Definitions.Def_OptimalRLS_Upper_Setting

open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace

namespace OptimalRLS.Upper

/-- **Proposition 1 v), (26)–(28)** (p. 12). For a training set `z ∈ Z^ℓ` (`ℓ ≥ 1`) and
`λ > 0`, the regularized empirical risk (18) has a unique minimizer `f_z^λ`, and it satisfies
`(T_x + λ) f_z^λ = g_z` with `T_x = (1/ℓ) ∑ K_{x_i} K_{x_i}^*` and `g_z = (1/ℓ) ∑ K_{x_i} y_i`
(`K_x^* f = f(x)` by (4)). -/
theorem proposition_1_v
    {X : Type*} [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
    {Y : Type*} [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
    [TopologicalSpace.SeparableSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H] [MeasurableSpace H] [BorelSpace H] [RKHS ℝ H X Y]
    {ι : Type*} (κ : ℝ) (v : HilbertBasis ι ℝ Y) (h1 : Hyp1 X H κ v)
    (lam : ℝ) (hlam : 0 < lam) {ℓ : ℕ} (hℓ : 1 ≤ ℓ) (z : Fin ℓ → X × Y) :
    (∃! f : H, IsRLSMin lam z f) ∧
      ∀ f : H, IsRLSMin lam z f →
        (1 / (ℓ : ℝ)) • ∑ i, RKHS.kerFun H (z i).1 (f (z i).1) + lam • f =
          (1 / (ℓ : ℝ)) • ∑ i, RKHS.kerFun H (z i).1 (z i).2 := by sorry

end OptimalRLS.Upper
