-- Prove2me | Theorems.Thm_OptRobustCD_theorem_8_1
-- name    : OptRobustCD.theorem_8_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T23:50:44.509413+00:00
-- url     : https://prove2.me/theorems/79b03542-f2d4-4562-808e-9b026d85a402
-- title:
--   Theorem 8.1 — matrix recovery: near-minimizers of $F$ over density matrices are close to $ww^T$
-- statement:
--   Let $n\ge2$, $K\ge1$, $g>0$ and $\varepsilon\ge0$. Suppose $M,E\in\mathbb R^{n\times n}$ are symmetric and $v,w\in\mathbb R^n$ are unit vectors with
--   $$M\succeq-gvv^T,\qquad n\|w\|_4^4\le K,\qquad w^TMw\le-(1-\varepsilon)g.$$
--   Set $A=M+E$, let $P\ge\|A\|_{1,\infty}$ and $F(X)=\langle A,X\rangle+P\cdot\mathrm{dist}_1(\mathrm{diag}X,\mathcal D_K)$. Then
--   $$\Bigl|\frac1g\min_{\mathcal S}F+1\Bigr|\le\varepsilon+\sqrt{K/n}\,\|E\|_{1,2}/g,$$
--   and every $X\in\mathcal S$ with $F(X)\le\min_{\mathcal S}F+\varepsilon g$ satisfies
--   $$\|X-ww^T\|_F^2\le20\Bigl(\varepsilon+\sqrt{K/n}\,\|E\|_{1,2}/g\Bigr).$$
--
--   This is the deterministic recovery guarantee behind Lemma 5.9: an approximate minimizer of a convex program recovers a delocalized negative eigenvector despite a perturbation small in $\|\cdot\|_{1,2}$.
--
--   Differences from the source:
--   - encoding: M ⪰ −gvv^T → M + g vv^T ⪰ 0; reason: the meaning of the Loewner order
--   - encoding: min_S F → the real infimum of F over S (minObj); reason: S is nonempty and compact and F is continuous, so the infimum is attained
-- source:
--   Hopkins, Hua, Mohanty, Rajaraman, Steurer, Optimal Robust Community Detection, STOC 2027 submission (manuscript of November 3, 2026, sha256 3d287d5422db7c4a43e74333bda1dbed204af51a25fd9f2c6e875ae03a4dafa1), Theorem 8.1, p.37 (pdf p.39)

import Mathlib
import Definitions.Def_OptRobustCD_DirEdges
import Definitions.Def_OptRobustCD_RowNorms
import Definitions.Def_OptRobustCD_SDPObjective

namespace OptRobustCD

/-- **Theorem 8.1** (Matrix recovery). Hopkins, Hua, Mohanty, Rajaraman, Steurer, *Optimal Robust
Community Detection*, STOC 2027 submission (manuscript of November 3, 2026, sha256 3d287d54…),
Theorem 8.1, p.37 (pdf p.39).

"Let K ⩾ 1, g > 0, and ε ⩾ 0. Suppose `M, E ∈ R^{n×n}` are symmetric and `v, w ∈ R^n` are unit
vectors satisfying `M ⪰ −gvv^T`, `n∥w∥⁴_4 ⩽ K`, `w^TMw ⩽ −(1 − ε)·g`. Set A = M + E and let
`P ⩾ ∥A∥_{1,∞}`. Define `F(X) = ⟨A, X⟩ + P · dist_1(diag X, D_K)`. Then
`|(1/g) min_S F + 1| ⩽ ε + √(K/n)∥E∥_{1,2}/g`, and every X ∈ S with `F(X) ⩽ min_S F + εg` satisfies
`∥X − ww^T∥²_F ⩽ 20(ε + √(K/n)∥E∥_{1,2}/g)`."

**Formalization Note.** Standing assumption of §8 (p.37): `n ⩾ 2`. `M ⪰ −gvv^T` is
`M + g vv^T ⪰ 0`. `min_S F` is `minObj`, the infimum of `F` over the density matrices (attained). -/
theorem theorem_8_1 {n : ℕ} (hn : 2 ≤ n) (K g ε : ℝ) (hK : 1 ≤ K) (hg : 0 < g) (hε : 0 ≤ ε)
    (M E : Matrix (Fin n) (Fin n) ℝ) (hM : M.IsSymm) (hE : E.IsSymm) (v w : Fin n → ℝ)
    (hv : l2 v = 1) (hw : l2 w = 1) (hMv : (M + g • Matrix.vecMulVec v v).PosSemidef)
    (hw4 : (n : ℝ) * l4pow4 w ≤ K) (hwM : w ⬝ᵥ M.mulVec w ≤ -(1 - ε) * g)
    (P : ℝ) (hP : norm1inf (M + E) ≤ P) :
    |(1 / g) * minObj (M + E) P K + 1| ≤ ε + Real.sqrt (K / n) * norm12 E / g ∧
    ∀ X ∈ densitySet n, objF (M + E) P K X ≤ minObj (M + E) P K + ε * g →
      frob2 (X - Matrix.vecMulVec w w) ≤ 20 * (ε + Real.sqrt (K / n) * norm12 E / g) := by sorry

end OptRobustCD
