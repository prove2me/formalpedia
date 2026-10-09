-- Prove2me | Theorems.Thm_HighOrderWalks_OneSided_lemma_5_1
-- name    : HighOrderWalks.OneSided.lemma_5_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T01:44:29.344107+00:00
-- url     : https://prove2.me/theorems/326fa266-2c52-4cc6-87f5-d6cc26bccfad
-- title:
--   Lemma 5.1, p. 14 — ker((d_{k−1})*) ⊆ C^k_0, and ψ ∈ C^{k−1}_0 ⇔ d_{k−1}ψ ∈ C^k_0
-- statement:
--   Let $X$ be a pure $n$-dimensional weighted simplicial complex and $0\le k\le n-1$. Write $C^j_0(X,\mathbb R)=\{\phi:\ \sum_{\sigma\in X(j)}m(\sigma)\phi(\sigma)=0\}$ for the $j$-cochains orthogonal to the constants. Then:
--   1. every $k$-cochain $\phi$ with $(d_{k-1})^*\phi=0$ on $X(k-1)$ lies in $C^k_0(X,\mathbb R)$, i.e. $\ker((d_{k-1})^*)\subseteq C^k_0(X,\mathbb R)$;
--   2. for every $(k-1)$-cochain $\psi$,
--   $$\psi\in C^{k-1}_0(X,\mathbb R)\iff d_{k-1}\psi\in C^k_0(X,\mathbb R).$$
--
--   This lemma lets the Decomposition Theorem split a cochain orthogonal to the constants into pieces that stay orthogonal to the constants.
--
--   **Formalization Note.** Orthogonality is weighted by $m$. At $k=0$ the space $C^{-1}_0$ (not defined on the page, which defines $C^j_0$ for $j\ge0$) is read by the same formula: $m(\emptyset)\psi(\emptyset)=0$.
-- source:
--   Kaufman–Oppenheim, High Order Random Walks: Beyond Spectral Gap, arXiv:1707.02799v3, p. 14, Lemma 5.1

import Mathlib
import Definitions.Def_HighOrderWalks_OneSided_Setting

namespace HighOrderWalks.OneSided

/-- Lemma 5.1, p. 14: for `0 ≤ k ≤ n - 1`, `ker((d_{k-1})*) ⊆ C^k_0(X, ℝ)`, and a
`(k-1)`-cochain `ψ` lies in `C^{k-1}_0(X, ℝ)` iff `d_{k-1}ψ ∈ C^k_0(X, ℝ)`. Membership in
`C^j_0` is weighted orthogonality to the constants. -/
theorem lemma_5_1 {V : Type*} [DecidableEq V] (X : Finset (Finset V)) (n : ℕ)
    (hX : IsPureComplex X n) (m : Finset V → ℝ) (hm : IsWeight X n m)
    (k : ℕ) (hk : k + 1 ≤ n) :
    (∀ φ : Finset V → ℝ, (∀ τ ∈ cells X k, dStar X m φ τ = 0) →
        ip X m (k + 1) φ (fun _ => 1) = 0) ∧
      ∀ ψ : Finset V → ℝ,
        ip X m k ψ (fun _ => 1) = 0 ↔ ip X m (k + 1) (dS X ψ) (fun _ => 1) = 0 := by sorry

end HighOrderWalks.OneSided
