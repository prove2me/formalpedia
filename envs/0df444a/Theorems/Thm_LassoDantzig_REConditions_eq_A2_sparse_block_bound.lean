-- Prove2me | Theorems.Thm_LassoDantzig_REConditions_eq_A2_sparse_block_bound
-- name    : LassoDantzig.REConditions.eq_A2_sparse_block_bound
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T10:12:40.194+00:00
-- url     : https://prove2.me/theorems/33d1c775-54ef-4ca1-90d1-76c9f703b17d
-- title:
--   (A.2) — Projected image of an $m$-sparse block is bounded by $\sqrt{\phi_{\max}(m)}$
-- statement:
--   Let $X\in\mathbb R^{n\times M}$, $m\ge1$, $\delta\in\mathbb R^M$, and let $J$ be an index set with $|J|\le m$, so that $\delta_J$ has at most $m$ non-zero components. Let $P$ be the orthogonal projector in $\mathbb R^n$ onto the span of the columns of $X_{J'}$ for an arbitrary index set $J'$ (in the proof, $J'=J_{01}$). Then
--
--   $$
--   \frac1{\sqrt n}|PX\delta_J|_2\ \le\ \frac1{\sqrt n}|X\delta_J|_2\ \le\ \sqrt{\phi_{\max}(m)}\,|\delta_J|_2 .
--   $$
--
--   This bounds each tail block's contribution in (A.1) in the proof of Lemma 4.1 (ii).
--
--   **Formalization Note** The paper applies the bound to the blocks $J_k$ of the Appendix A partition and to $P=P_{01}$; the statement here is for any $J$ with $|J|\le m$ and any column span, which is what the argument uses. $n\ge1$, $M\ge2$ are standing assumptions.
-- source:
--   Bickel, Ritov and Tsybakov, Simultaneous Analysis of Lasso and Dantzig Selector, arXiv:0801.1095v3, p. 19, Appendix A, Eq. (A.2)

import Mathlib
import Definitions.Def_LassoDantzig_REConditions_RE
import Definitions.Def_LassoDantzig_REConditions_RestrictedEigenvalues

namespace LassoDantzig.REConditions

/-- **(A.2)**, Bickel–Ritov–Tsybakov, arXiv:0801.1095v3, Appendix A, p. 19. If `|J| ≤ m` (so
`δ_J` has at most `m` non-zero components), then for the orthogonal projector `P_{J'}` onto the
span of the columns of `X_{J'}` (any `J'`, in particular `J' = J01`):
`(1/√n)|P_{J'} X δ_J|₂ ≤ (1/√n)|X δ_J|₂ ≤ √φ_max(m) |δ_J|₂`. -/
theorem eq_A2_sparse_block_bound {n M : ℕ} (X : Matrix (Fin n) (Fin M) ℝ)
    (hn : 1 ≤ n) (hM : 2 ≤ M) (m : ℕ) (hm : 1 ≤ m)
    (δ : Fin M → ℝ) (J J' : Finset (Fin M)) (hJ : J.card ≤ m) :
    1 / Real.sqrt n * projNorm X J' (X.mulVec (restrict δ J)) ≤
        1 / Real.sqrt n * euclNorm (X.mulVec (restrict δ J)) ∧
    1 / Real.sqrt n * euclNorm (X.mulVec (restrict δ J)) ≤
        Real.sqrt (phiMax X m) * l2On δ J := by sorry

end LassoDantzig.REConditions
