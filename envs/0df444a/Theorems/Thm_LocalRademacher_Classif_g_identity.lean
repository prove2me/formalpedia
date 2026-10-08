-- Prove2me | Theorems.Thm_LocalRademacher_Classif_g_identity
-- name    : LocalRademacher.Classif.g_identity
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T11:47:38.339986+00:00
-- url     : https://prove2.me/theorems/e4f9efac-97d8-4b83-8f9f-f678814679a6
-- title:
--   Proof of Theorem 6.3, p. 30 (corrected) — g(μ) = J(μ) − (1/2n)Σᵢ|σᵢ + μYᵢ| + (1 + μ)/2 − μ·2r/α²
-- statement:
--   Let $X_1,\dots,X_n$ be fixed inputs ($n\ge1$) with labels $Y_i\in\{-1,1\}$, let $\mathcal F$ be a nonempty class of $\{-1,1\}$-valued classifiers, $\ell$ the discrete loss and $P_n\ell(f(X),z)=\frac1n\sum_i\ell(f(X_i),z_i)$. Fix a sign vector $\sigma\in\{-1,1\}^n$, reals $r,\alpha$ and $\mu\ge0$, and let
--   $$g(\mu)=\min_{f\in\mathcal F}\Big(P_n\ell(f(X),\sigma)+\mu\Big(P_n\ell(f(X),Y)-\frac{2r}{\alpha^2}\Big)\Big),\qquad J(\mu)=\min_{f\in\mathcal F}\frac1n\sum_{i=1}^n|\sigma_i+\mu Y_i|\,\ell\big(f(X_i),\operatorname{sign}(\sigma_i+\mu Y_i)\big).$$
--   Then
--   $$g(\mu)=\min_{f\in\mathcal F}\frac1n\sum_{i=1}^n\big(\ell(f(X_i),\sigma_i)+\mu\,\ell(f(X_i),Y_i)\big)-\mu\frac{2r}{\alpha^2}
--   =J(\mu)-\frac1{2n}\sum_{i=1}^n|\sigma_i+\mu Y_i|+\frac{1+\mu}2-\mu\frac{2r}{\alpha^2}.$$
--
--   The identity rewrites the Lagrangian dual function of the localized problem as a weighted empirical risk minimization with corrupted labels $\operatorname{sign}(\sigma_i+\mu Y_i)$ and weights $|\sigma_i+\mu Y_i|$, which is what makes the bound of Theorem 6.3 computable by an empirical risk minimizer.
--
--   **Formalization Note** The page's display ends every line with $-2r/\alpha^2$; with $g(\mu)=\min_f L(f,\mu)$ as the page defines it, the constant term is $-\mu\,2r/\alpha^2$, and only this corrected form gives the term $(2r/\alpha^2-1/2)\mu$ of Theorem 6.3. The statement here is the corrected one. The page's two middle lines (which substitute $\ell(y,\hat y)=(1-y\hat y)/2$) are steps of the proof and are not stated separately. $F$ nonempty is required: for $F=\emptyset$ Lean's infima are $0$ and the two sides differ by $(1+\mu)/2$. Lean's `Real.sign 0 = 0` where the page's sign is undefined; that term has weight $0$.
-- source:
--   Bartlett, Bousquet & Mendelson, arXiv:math/0508275v1, Proof of Theorem 6.3, p. 30, last display (with g(μ) as defined in the third display)

import Mathlib
import Definitions.Def_UnderstandingML_Rademacher
import Definitions.Def_LocalRademacher_Classif_Setting

namespace LocalRademacher.Classif

/-- **The identity for `g(μ)`** in the proof of Theorem 6.3 (Bartlett, Bousquet & Mendelson,
arXiv:math/0508275v1, p. 30), corrected. For a fixed sign vector `σ`, `μ ≥ 0` and a nonempty
class `F` of `{±1}`-valued classifiers, with
`g(μ) = min_{f ∈ F} (Pₙℓ(f(X), σ) + μ (Pₙℓ(f(X), Y) − 2r/α²))`,
`g(μ) = min_{f ∈ F} (1/n) ∑ᵢ (ℓ(f(Xᵢ), σᵢ) + μ ℓ(f(Xᵢ), Yᵢ)) − μ·2r/α²
      = J(μ) − (1/2n) ∑ᵢ |σᵢ + μYᵢ| + (1 + μ)/2 − μ·2r/α²`.
The page prints `− 2r/α²` where the definition of `g` gives `− μ·2r/α²`; Theorem 6.3's term
`(2r/α² − 1/2)μ` requires the corrected form. -/
theorem g_identity {X : Type*} (n : ℕ) (hn : 0 < n) (xs : Fin n → X) (ys : Fin n → ℝ)
    (hys : ∀ i, ys i = 1 ∨ ys i = -1)
    (F : Set (X → ℝ)) (hF : ∀ f ∈ F, ∀ z, f z = 1 ∨ f z = -1) (hFne : F.Nonempty)
    (σ : Fin n → Bool) (r α μ : ℝ) (hμ : 0 ≤ μ) :
    (⨅ f : F, (empLoss xs (UnderstandingML.signVec σ) f.1
        + μ * (empLoss xs ys f.1 - 2 * r / α ^ 2))) =
      (⨅ f : F, (1 / (n : ℝ)) * ∑ i, (ell (f.1 (xs i)) (UnderstandingML.signVec σ i)
        + μ * ell (f.1 (xs i)) (ys i))) - μ * (2 * r / α ^ 2) ∧
    (⨅ f : F, (1 / (n : ℝ)) * ∑ i, (ell (f.1 (xs i)) (UnderstandingML.signVec σ i)
        + μ * ell (f.1 (xs i)) (ys i))) - μ * (2 * r / α ^ 2) =
      J F xs ys σ μ - (1 / (2 * (n : ℝ))) * ∑ i, |UnderstandingML.signVec σ i + μ * ys i|
        + (1 + μ) / 2 - μ * (2 * r / α ^ 2) := by sorry

end LocalRademacher.Classif
