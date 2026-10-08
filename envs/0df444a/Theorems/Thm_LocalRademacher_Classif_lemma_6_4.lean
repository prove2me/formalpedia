-- Prove2me | Theorems.Thm_LocalRademacher_Classif_lemma_6_4
-- name    : LocalRademacher.Classif.lemma_6_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T11:47:28.763487+00:00
-- url     : https://prove2.me/theorems/53939a58-fe01-4bf1-954e-6b3285b9a251
-- title:
--   Lemma 6.4, p. 29 — E_σRₙ{ℓ_f : f ∈ F, Pₙℓ_f ≤ b} = 1/2 − E_σ min{Pₙℓ(f(X),σ) : f ∈ F, Pₙℓ(f(X),Y) ≤ b}
-- statement:
--   Let $X_1,\dots,X_n$ be fixed inputs ($n\ge1$) with labels $Y_1,\dots,Y_n\in\{-1,1\}$, let $\mathcal F$ be a class of classifiers with values in $\{-1,1\}$, and let $\ell(y,y')=\mathbf 1[y\ne y']$ be the discrete loss. Write $P_n\ell(f(X),z)=\frac1n\sum_i\ell(f(X_i),z_i)$ and $P_n\ell_f=P_n\ell(f(X),Y)$. For every $b\in[0,1]$ such that some $f\in\mathcal F$ has $P_n\ell_f\le b$,
--   $$\mathbb E_\sigma R_n\{\ell_f : f\in\mathcal F,\ P_n\ell_f\le b\}=\frac12-\mathbb E_\sigma\min\{P_n\ell(f(X),\sigma) : f\in\mathcal F,\ P_n\ell(f(X),Y)\le b\},$$
--   where $\mathbb E_\sigma$ is the average over the $2^n$ sign vectors $\sigma\in\{-1,1\}^n$ and the left side is $\frac1n\mathbb E_\sigma\sup_f\sum_i\sigma_i\ell(f(X_i),Y_i)$ over the same feasible $f$.
--
--   The lemma turns the local Rademacher average of the loss class into the expected value of a constrained empirical risk minimization problem in which the labels are replaced by random signs. It is the first step of the proof of Theorem 6.3.
--
--   **Formalization Note** The page writes "for every $b\in[0,1]$" without requiring a feasible $f$; the hypothesis that some $f\in\mathcal F$ has $P_n\ell_f\le b$ is added because the page's $\min$ presupposes a nonempty feasible set (with no feasible $f$, Lean's left side would be $0$ and its right side $1/2$). The minimum is the real infimum over the subtype of feasible classifiers; it is attained because the empirical losses take finitely many values. The Rademacher average is the published `UnderstandingML.rademacher` of the set of loss vectors.
-- source:
--   Bartlett, Bousquet & Mendelson, arXiv:math/0508275v1, Lemma 6.4, p. 29 (proof pp. 29–30)

import Mathlib
import Definitions.Def_UnderstandingML_Rademacher
import Definitions.Def_LocalRademacher_Classif_Setting

namespace LocalRademacher.Classif

/-- **Lemma 6.4** (Bartlett, Bousquet & Mendelson, arXiv:math/0508275v1, p. 29). For labels
`Yᵢ ∈ {±1}`, a class `F` of `{±1}`-valued classifiers and every `b ∈ [0, 1]` for which some
`f ∈ F` has `Pₙℓ_f ≤ b`,
`E_σ Rₙ{ℓ_f : f ∈ F, Pₙℓ_f ≤ b} = 1/2 − E_σ min{Pₙℓ(f(X), σ) : f ∈ F, Pₙℓ(f(X), Y) ≤ b}`,
both expectations being the average over the `2ⁿ` sign vectors. The feasibility hypothesis
`hfeas` is added: the page's `min` presupposes a nonempty feasible set. -/
theorem lemma_6_4 {X : Type*} (n : ℕ) (hn : 0 < n) (xs : Fin n → X) (ys : Fin n → ℝ)
    (hys : ∀ i, ys i = 1 ∨ ys i = -1)
    (F : Set (X → ℝ)) (hF : ∀ f ∈ F, ∀ z, f z = 1 ∨ f z = -1)
    (b : ℝ) (hb0 : 0 ≤ b) (hb1 : b ≤ 1)
    (hfeas : ∃ f ∈ F, empLoss xs ys f ≤ b) :
    UnderstandingML.rademacher (lossVecs F xs ys b) =
      1 / 2 - (1 / 2 ^ n : ℝ) * ∑ σ : Fin n → Bool,
        ⨅ f : {f : X → ℝ // f ∈ F ∧ empLoss xs ys f ≤ b},
          empLoss xs (UnderstandingML.signVec σ) f.1 := by sorry

end LocalRademacher.Classif
