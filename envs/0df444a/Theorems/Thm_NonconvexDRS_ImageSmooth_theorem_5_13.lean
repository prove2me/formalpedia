-- Prove2me | Theorems.Thm_NonconvexDRS_ImageSmooth_theorem_5_13
-- name    : NonconvexDRS.ImageSmooth.theorem_5_13
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T15:38:28.02384+00:00
-- url     : https://prove2.me/theorems/bde66a85-cfdf-4704-b321-1459d101c3ac
-- title:
--   Theorem 5.13, p. 25 — (Af) is smooth if f is smooth relative to A, or C^{1,1} with Lipschitz single-valued minimizers, or C^{1,1} and convex
-- statement:
--   **Theorem 5.13 (Smoothness of $(Af)$).** Let $A\in\mathbb R^{p\times n}$ be surjective and $f:\mathbb R^n\to\mathbb R$ lower semicontinuous. Suppose there exists $\beta\ge0$ such that the function $f+\frac\beta2\|A\cdot-s\|^2$ is level bounded for all $s\in\mathbb R^p$. Then the image function
--   $$(Af)(s)=\inf\{f(x)\mid Ax=s\}$$
--   is smooth on $\mathbb R^p$ (real-valued, $L_{(Af)}$-smooth and $\sigma_{(Af)}$-hypoconvex), provided that either
--
--   1. $f\in C^{1,1}_A(\mathbb R^n)$ is smooth relative to $A$ with constants $L_{f,A}$, $\sigma_{f,A}$ (Definition 5.12), in which case $L_{(Af)}=L_{f,A}$ and $\sigma_{(Af)}=\sigma_{f,A}$;
--   2. or $f\in C^{1,1}(\mathbb R^n)$ is $L_f$-smooth and $\sigma_f$-hypoconvex with $\sigma_f\in[-L_f,L_f]$, and $X(s)=\operatorname*{arg\,min}\{f(x)\mid Ax=s\}$ is single valued and Lipschitz continuous with modulus $M$, in which case
--   $$L_{(Af)}=L_fM^2\qquad\text{and}\qquad\sigma_{(Af)}=\begin{cases}\sigma_f/\|A\|^2&\text{if }\sigma_f\ge0,\\ \sigma_fM^2&\text{if }\sigma_f<0;\end{cases}$$
--   3. or $f\in C^{1,1}(\mathbb R^n)$, $L_f$-smooth and $\sigma_f$-hypoconvex with $\sigma_f\in[-L_f,L_f]$, is convex, in which case
--   $$L_{(Af)}=\frac{L_f}{\sigma_+(A^\top A)}\qquad\text{and}\qquad\sigma_{(Af)}=\frac{\sigma_f}{\|A\|^2},$$
--   where $\sigma_+(A^\top A)$ is the smallest nonzero singular value of $A^\top A$.
--
--   In the primal equivalence of ADMM and DRS (Theorem 5.5) ADMM is DRS applied to $\varphi_1=(Af)$, and the convergence theory of DRS requires $\varphi_1$ to be smooth. This theorem gives three checkable conditions on $f$ and $A$ under which this holds, with explicit constants.
--
--   **Formalization Note** The three cases are three separate implications, each with its own constants. Case (ii): "$X(s)$ single valued" is the existence of a map $X$ with $AX(s)=s$ and $X(s)$ minimizing $f$ on the fibre, every fibre minimizer being $X(s)$; "Lipschitz with modulus $M$" is $\|X(s)-X(s')\|\le M\|s-s'\|$. Case (iii): for surjective $A$ the nonzero eigenvalues of $A^\top A$ are those of $AA^\top$, so $\sigma_+(A^\top A)=\min_{\|y\|=1}\|A^\top y\|^2$; this value is passed as an argument $c$ with the hypothesis that $c$ is the least element of $\{\|A^\top y\|^2:\|y\|=1\}$. For $p=0$ that set is empty and case (iii) is vacuous, matching the page, where $\sigma_+$ of the zero matrix is undefined; also for $p=0$ Lean's $\sigma_f/\|A\|^2=\sigma_f/0=0$, and every function on a single point is smooth, so the statement is trivially true there, as on the page. The goal does not assume $(Af)$ real-valued, differentiable, or strictly continuous, nor any existence of minimizers beyond case (ii)'s hypothesis.
-- source:
--   Themelis & Patrinos, Douglas-Rachford splitting and ADMM for nonconvex optimization: tight convergence results, arXiv:1709.05747v4, p. 25, Theorem 5.13 (proof pp. 25–26); σ₊ notation p. 5

import Mathlib
import Definitions.Def_NonconvexSplitting_Shared_LimitingSubdiff
import Definitions.Def_NonconvexDRS_ImageSmooth_Setting

open NonconvexSplitting.Shared
open scoped InnerProductSpace

namespace NonconvexDRS.ImageSmooth

/-- Theorem 5.13 (Smoothness of `(Af)`), p. 25. Let `A ∈ ℝ^{p×n}` be surjective and `f : ℝⁿ → ℝ`
lsc, and suppose that for some `β ≥ 0` the function `f + (β/2)‖A · - s‖²` is level bounded for
every `s ∈ ℝᵖ`. Then `(Af)` is smooth on `ℝᵖ` provided that either
(i) `f ∈ C^{1,1}_A(ℝⁿ)`, with `L_{(Af)} = L_{f,A}`, `σ_{(Af)} = σ_{f,A}`;
(ii) `f ∈ C^{1,1}(ℝⁿ)` and `X(s) = argmin {f(x) | Ax = s}` is single valued and `M`-Lipschitz, with
`L_{(Af)} = L_f M²` and `σ_{(Af)} = σ_f/‖A‖²` if `σ_f ≥ 0`, `σ_f M²` if `σ_f < 0`;
(iii) `f ∈ C^{1,1}(ℝⁿ)` is convex, with `L_{(Af)} = L_f/σ₊(AᵀA)` and `σ_{(Af)} = σ_f/‖A‖²`,
where `σ₊(AᵀA) = c` is the least value of `‖Aᵀy‖²` over unit vectors `y`. -/
theorem theorem_5_13 {n p : ℕ}
    (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin p)) (hA : Function.Surjective A)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : LowerSemicontinuous f)
    (hlev : ∃ β : ℝ, 0 ≤ β ∧ ∀ s : EuclideanSpace ℝ (Fin p), ∀ α : ℝ,
      Bornology.IsBounded {x | f x + β / 2 * ‖A x - s‖ ^ 2 ≤ α}) :
    (∀ L σ : ℝ, IsSmoothRel f A L σ → IsImageSmooth A f L σ) ∧
    (∀ Lf σf M : ℝ, NonconvexDRS.DRS.IsLSmooth f Lf → NonconvexDRS.DRS.IsHypoconvex f σf → -Lf ≤ σf → σf ≤ Lf →
      (∃ X : EuclideanSpace ℝ (Fin p) → EuclideanSpace ℝ (Fin n),
        (∀ s, A (X s) = s ∧ ∀ x, A x = s → f (X s) ≤ f x) ∧
        (∀ s x, A x = s → (∀ x', A x' = s → f x ≤ f x') → x = X s) ∧
        ∀ s s', ‖X s - X s'‖ ≤ M * ‖s - s'‖) →
      IsImageSmooth A f (Lf * M ^ 2) (if 0 ≤ σf then σf / ‖A‖ ^ 2 else σf * M ^ 2)) ∧
    (∀ Lf σf c : ℝ, ConvexOn ℝ Set.univ f → NonconvexDRS.DRS.IsLSmooth f Lf → NonconvexDRS.DRS.IsHypoconvex f σf →
      -Lf ≤ σf → σf ≤ Lf →
      IsLeast {t | ∃ y : EuclideanSpace ℝ (Fin p), ‖y‖ = 1 ∧
        t = ‖ContinuousLinearMap.adjoint A y‖ ^ 2} c →
      IsImageSmooth A f (Lf / c) (σf / ‖A‖ ^ 2)) := by sorry

end NonconvexDRS.ImageSmooth
