-- Prove2me | Theorems.Thm_MakespanSparse_Thin_sparsification_lemma
-- name    : MakespanSparse.Thin.sparsification_lemma
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T23:04:02.985752+00:00
-- url     : https://prove2.me/theorems/bb3ae6f3-5b4b-4b76-815a-f1eaad6effab
-- title:
--   Lemma 4, p. 5 — Sparsification Lemma: a complex c has 2c = c₁ + c₂ with π·c₁ = π·c₂ = π·c and supp(cᵢ) ⊊ supp(c)
-- statement:
--   Let $\pi \in \mathbb{Z}^d_{>0}$ and $T \in \mathbb{N}$, and let $Q$ be the set of configurations $c \in \mathbb{Z}^d_{\ge 0}$ with $\pi \cdot c \le T$. Call $c$ *complex* if $|\operatorname{supp}(c)| > \log_2(T+1)$. Let $c \in Q$ be a complex configuration. Then there exist two configurations $c_1, c_2 \in Q$ such that
--
--   1. $\pi \cdot c_1 = \pi \cdot c_2 = \pi \cdot c$,
--   2. $2c = c_1 + c_2$,
--   3. $\operatorname{supp}(c_1) \subsetneq \operatorname{supp}(c)$ and $\operatorname{supp}(c_2) \subsetneq \operatorname{supp}(c)$.
--
--   $$2c = c_1 + c_2, \qquad \operatorname{supp}(c_i) \subsetneq \operatorname{supp}(c).$$
--
--   The lemma says that two copies of a complex machine packing can always be repacked into two packings of the same load with strictly smaller support; it drives the potential argument for thin solutions.
--
--   **Formalization Note** The positivity of $T$ is not needed for this statement and is not assumed, which makes it slightly more general than the paper's setting. $2c$ is the pointwise double of $c$, and $\subsetneq$ is strict inclusion of finite sets of coordinates.
-- source:
--   arXiv:1604.07153v1, Lemma 4 (Sparsification Lemma), p. 5

import Mathlib
import Definitions.Def_MakespanSparse_Thin_ConfIP

namespace MakespanSparse.Thin

/-- Lemma 4 (Sparsification Lemma), arXiv:1604.07153v1, p. 5. -/
theorem sparsification_lemma (d : ℕ) (π : Fin d → ℕ) (hπ : ∀ k, 0 < π k) (T : ℕ)
    (c : Fin d → ℕ) (hc : IsConfig π T c) (hcx : ¬ IsSimple T c) :
    ∃ c₁ c₂ : Fin d → ℕ, IsConfig π T c₁ ∧ IsConfig π T c₂ ∧
      ∑ k, π k * c₁ k = ∑ k, π k * c k ∧ ∑ k, π k * c₂ k = ∑ k, π k * c k ∧
      2 • c = c₁ + c₂ ∧ supp c₁ ⊂ supp c ∧ supp c₂ ⊂ supp c := by sorry

end MakespanSparse.Thin
