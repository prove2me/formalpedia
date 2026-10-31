-- Prove2me | Theorems.Thm_LowRankIndicator_support_Q_le
-- name    : LowRankIndicator.support_Q_le
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:18:49.195993+00:00
-- url     : https://prove2.me/theorems/55c2f021-98f2-4104-bb83-fbcc6e45e64e
-- title:
--   Proof of Theorem 1, pp.7–8 — $\delta^*(\alpha;S)\ge\delta^*(\alpha;Q)$, and the same with $R$ removed under the cone hypothesis (corrected: $R$ uses $t\ge c^\top x$)
-- statement:
--   Let $f(x)=g(Ax)+c^\top x$ with $A$ a $k\times n$ matrix and $f(0)=0$, and let $S=\bigl(\bigcup_{I:|I|\le k}V(I)\bigr)\cup R$. For every continuous linear functional $\alpha$ on $\mathbb R\times\mathbb R^n\times\mathbb R^n$,
--
--   $$\delta^*(\alpha;Q)\le\delta^*(\alpha;S).$$
--
--   If moreover $\{x\in\mathbb R^n:Ax=0,\ x_i\ge0\ \forall i\in I_+\}=\{0\}$, then for every such $\alpha$,
--
--   $$\delta^*(\alpha;Q)\le\delta^*\Bigl(\alpha;\bigcup_{I:|I|\le k}V(I)\Bigr).$$
--
--   These two inequalities are the content of the main theorem once the support function characterization of closed convex hulls is applied.
--
--   **Formalization Note** The support function has values in $[-\infty,+\infty]$. The hypothesis $f(0)=0$ is that of Theorem 1.
--
--   Differences from the source:
--   - correction: R = {t ≥ 0, Ax = 0, xᵢ ≥ 0 ∀i ∈ I₊, zᵢ = 1 ∀i} in (5) → t ≥ c⊤x in place of t ≥ 0; reason: the printed R is not contained in Q, as for n = k = 1, A = 0, g ≡ 0, c = 1, I₊ = ∅ at (0, 1, 1); the proof itself uses (rc⊤d, rd, e) ∈ R, and the sets agree for c = 0
--   - reading: rank(f) ≤ k, "there exists g(·), A ∈ Rk×n and c" → the statement holds for every (g, A, c) with A having k rows; reason: R and the cone depend on the matrix A of a representation, so the representation is a parameter; a representation with fewer rows is padded by zero rows
--   - generalization: g proper closed convex → arbitrary g : ℝᵏ → `EReal` with f(0) = 0; reason: the statement holds without these properties and specializes to the paper's g
--   - encoding: α = (αₜ, αₓ, α_z) and max → continuous linear functional φ on `Point n` and `EReal`-valued supremum; reason: every such functional is α⊤·, and the supremum may be infinite
-- source:
--   Han & Gómez, Compact Extended Formulations for Low-Rank Functions with Indicator Variables, arXiv:2110.14884v2, proof of Theorem 1, pp.7–8, "δ∗(α; S) ≥ δ∗(α; Q)" and "The last statement of the theorem follows", p.8.

import Mathlib
import Definitions.Def_LowRankIndicator_Sets
import Definitions.Def_VectorSpaceOpt_support_functional

namespace LowRankIndicator

/-- Han & Gómez, arXiv:2110.14884v2, proof of Theorem 1, pp.7–8, "δ∗(α; S) ≥ δ∗(α; Q)", with
`S = (⋃_{I:|I|≤k} V(I)) ∪ R`; and, under the cone hypothesis of the theorem's last statement, the
same inequality with `R` removed from `S`.

**Formalization Note.** `R` is the corrected set `t ≥ c⊤x`. `δ∗` is the `EReal`-valued
`VectorSpaceOpt_support_functional` and `α` is a continuous linear functional `φ`. `g` is an
arbitrary `EReal`-valued function. -/
theorem support_Q_le {n k : ℕ} (g : (Fin k → ℝ) → EReal) (A : Matrix (Fin k) (Fin n) ℝ)
    (c : Fin n → ℝ) (Iplus : Set (Fin n)) (hf : objective g A c 0 = 0) :
    (∀ φ : Point n →L[ℝ] ℝ,
      VectorSpaceOpt_support_functional (Q g A c Iplus) φ ≤
        VectorSpaceOpt_support_functional (lowRankPieces g A c Iplus ∪ R A c Iplus) φ) ∧
    (recCone A Iplus = {0} → ∀ φ : Point n →L[ℝ] ℝ,
      VectorSpaceOpt_support_functional (Q g A c Iplus) φ ≤
        VectorSpaceOpt_support_functional (lowRankPieces g A c Iplus) φ) := by sorry

end LowRankIndicator
