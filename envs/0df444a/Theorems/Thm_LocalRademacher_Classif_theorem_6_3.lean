-- Prove2me | Theorems.Thm_LocalRademacher_Classif_theorem_6_3
-- name    : LocalRademacher.Classif.theorem_6_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T11:47:41.357835+00:00
-- url     : https://prove2.me/theorems/a76222c0-93f1-4161-bdc5-a72a6ff11052
-- title:
--   Theorem 6.3, pp. 28–29 — ψ̂ₙ(r) ≤ c sup_α α E_σ min_{μ≥0}((2r/α² − 1/2)μ + (1/2n)Σᵢ|σᵢ + μYᵢ| − J(μ)) + 26x/n
-- statement:
--   Let $X_1,\dots,X_n$ be fixed inputs ($n\ge1$) with labels $Y_1,\dots,Y_n\in\{-1,1\}$, let $\mathcal F$ be a class of classifiers with values in $\{-1,1\}$, and let $\ell(y,y')=\mathbf 1[y\ne y']$ be the discrete loss, with $P_n\ell_f=\frac1n\sum_i\ell(f(X_i),Y_i)$. For $c\ge0$, $x>0$ and $0<r\le 1/2$, the empirical local Rademacher complexity of the classification loss class (Corollary 6.2) is
--   $$\hat\psi_n(r)=c\sup_{\alpha\in[\sqrt{2r},1]}\alpha\,\mathbb E_\sigma R_n\{\ell_f : f\in\mathcal F,\ P_n\ell_f\le 2r/\alpha^2\}+\frac{26x}{n}.$$
--   For a sign vector $\sigma\in\{-1,1\}^n$ and $\mu\ge0$ let
--   $$J(\mu)=\min_{f\in\mathcal F}\frac1n\sum_{i=1}^n|\sigma_i+\mu Y_i|\,\ell\big(f(X_i),\operatorname{sign}(\sigma_i+\mu Y_i)\big).$$
--   If some $f\in\mathcal F$ has $P_n\ell_f\le 2r$, then
--   $$\hat\psi_n(r)\le c\sup_{\alpha\in[\sqrt{2r},1]}\alpha\,\mathbb E_\sigma\min_{\mu\ge0}\Big(\Big(\frac{2r}{\alpha^2}-\frac12\Big)\mu+\frac1{2n}\sum_{i=1}^n|\sigma_i+\mu Y_i|-J(\mu)\Big)+\frac{26x}{n},$$
--   where $\mathbb E_\sigma$ is the average over the $2^n$ sign vectors on both sides.
--
--   The theorem says that an upper bound on the localized complexity $\hat\psi_n$ can be computed whenever one can minimize a weighted empirical classification error: for each sign vector and each $\mu$, $J(\mu)$ is the optimal value of a weighted classification problem with labels corrupted by the signs. Combined with Corollary 6.2, this gives computable data-dependent error bounds for empirical risk minimization in classification.
--
--   **Formalization Note** Three hypotheses implicit on the page are added: $c\ge0$ (the multiplier, $20$ in Corollary 6.2; for $c<0$ the inequality reverses); $0<r\le 1/2$, so that the range $[\sqrt{2r},1]$ of $\alpha$ is nonempty and $2r/\alpha^2$ is finite; and a classifier with $P_n\ell_f\le 2r$, so that every minimum on the page is over a nonempty set (since $\alpha\le1$, such an $f$ is feasible at every level $2r/\alpha^2$). The suprema and minima are Lean's real suprema and infima over subtypes, which these hypotheses make nonempty and bounded. $x>0$ is Corollary 6.2's "fix $x>0$"; the term $26x/n$ is kept on both sides as printed. Lean's `Real.sign 0 = 0` where the page's sign is undefined; that term has weight $0$.
-- source:
--   Bartlett, Bousquet & Mendelson, arXiv:math/0508275v1, Theorem 6.3, pp. 28–29 (ψ̂ₙ from Corollary 6.2, p. 28); proof p. 30

import Mathlib
import Definitions.Def_UnderstandingML_Rademacher
import Definitions.Def_LocalRademacher_Classif_Setting

namespace LocalRademacher.Classif

/-- **Theorem 6.3** (Bartlett, Bousquet & Mendelson, arXiv:math/0508275v1, pp. 28–29). For labels
`Yᵢ ∈ {±1}`, a class `F` of `{±1}`-valued classifiers, `c ≥ 0`, `x > 0` and `0 < r ≤ 1/2` such that
some `f ∈ F` has `Pₙℓ_f ≤ 2r`, the empirical local Rademacher complexity of the classification
loss class satisfies
`ψ̂ₙ(r) ≤ c sup_{α ∈ [√(2r), 1]} α E_σ min_{μ ≥ 0} ((2r/α² − 1/2)μ + (1/2n) ∑ᵢ |σᵢ + μYᵢ| − J(μ)) + 26x/n`,
`E_σ` being the average over the `2ⁿ` sign vectors. The hypotheses `0 ≤ c`, `0 < r ≤ 1/2` and the
feasibility hypothesis `hfeas` are implicit on the page and added here. -/
theorem theorem_6_3 {X : Type*} (n : ℕ) (hn : 0 < n) (xs : Fin n → X) (ys : Fin n → ℝ)
    (hys : ∀ i, ys i = 1 ∨ ys i = -1)
    (F : Set (X → ℝ)) (hF : ∀ f ∈ F, ∀ z, f z = 1 ∨ f z = -1)
    (c x r : ℝ) (hc : 0 ≤ c) (hx : 0 < x) (hr : 0 < r) (hr2 : r ≤ 1 / 2)
    (hfeas : ∃ f ∈ F, empLoss xs ys f ≤ 2 * r) :
    psiHat c x r F xs ys ≤
      c * (⨆ α : Set.Icc (Real.sqrt (2 * r)) 1,
          (α : ℝ) * ((1 / 2 ^ n : ℝ) * ∑ σ : Fin n → Bool,
            ⨅ μ : Set.Ici (0 : ℝ),
              ((2 * r / (α : ℝ) ^ 2 - 1 / 2) * (μ : ℝ)
                + (1 / (2 * (n : ℝ))) * ∑ i, |UnderstandingML.signVec σ i + (μ : ℝ) * ys i|
                - J F xs ys σ μ)))
        + 26 * x / n := by sorry

end LocalRademacher.Classif
