-- Prove2me | Theorems.Thm_LpSubspaceCoreset_SmallP_lemma_3_2
-- name    : LpSubspaceCoreset.SmallP.lemma_3_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T01:48:03.138204+00:00
-- url     : https://prove2.me/theorems/63088585-e49d-4cc1-b04b-c8c066b5f48e
-- title:
--   Lemma 3.2 — balanced sensitivity for a low-rank split
-- statement:
--   Fix $1\le p<2$ and $\Gamma\ge1$. There is a constant $C_{p,\Gamma}$ such that the following holds. Let $k\ge1$, $A=B+E\in\mathbb R^{n\times d}$ with $r=\operatorname{rank}B$ and $R=\|E\|_{p,2}^p=\sum_i\|e_i\|_2^p\le\Gamma\,\mathrm{OPT}_A$ (split (3.1)), $R>0$; let $\rho_i=\|e_i\|_2^p/R$, let $w_i$ be the Lewis weights of the rows $b_i$ ($w_i=0$ when $b_i=0$), $D=k+r$ and
--   $$s_i=w_i+D\rho_i.\qquad(3.3)$$
--   Then $\|Q_Fa_i\|_2^p\le C_{p,\Gamma}\,s_i\sum_j\|Q_Fa_j\|_2^p$ for every $F\in\mathcal F_k$ and every $i$; and with $S=\sum_is_i$ and $q_i=s_i/S$,
--   $$S\le2D,\qquad q_i\ge\frac{w_i}{2D},\qquad q_i\ge\frac{\rho_i}2.$$
--   It supplies the sampling distribution of Theorem 3.1.
--
--   Differences from the source:
--   - reading: k as in the problem (1 ≤ k < d, §1.2; Theorem 3.1 assumes k ≥ 1) → hypothesis 1 ≤ k; reason: standing assumption of §3; at k = r = 0 the lemma is false (s_i = 0 while ‖Q_F a_i‖ > 0)
--   - encoding: C_{p,Γ} → ∃ C chosen after p, Γ and before n, d, k, A, B, E, w; reason: constant depending only on p and Γ
-- source:
--   Lin, Mirrokni, Woodruff, Nearly Optimal Strong Coresets for ℓp Subspace Approximation, arXiv:2608.26047 (held PDF of 2026-11-03, sha256 4c61606e…), p. 16, Lemma 3.2

import Mathlib
import Definitions.Def_LpSubspaceCoreset_SmallP_Cost
import Definitions.Def_LpSubspaceCoreset_SmallP_Lewis

namespace LpSubspaceCoreset.SmallP

/-- **Lemma 3.2** (Balanced sensitivity for a low-rank split), p. 16.

Fix `1 ≤ p < 2` and `Γ ≥ 1`; there is `C_{p,Γ}` such that the following holds. Let `k ≥ 1` and
`A = B + E` with `r = rank(B)` and `R = ‖E‖_{p,2}^p = Σ_i ‖e_i‖₂^p ≤ Γ·OPT_A`, `R > 0` (split
(3.1)). Let `ρ_i = ‖e_i‖₂^p/R`, let `w_i` be the Lewis weights of the rows `b_i` of `B` (`w_i = 0`
when `b_i = 0`), `D = k + r` and `s_i = w_i + Dρ_i` (3.3). Then
`‖Q_F a_i‖₂^p ≤ C_{p,Γ} s_i Σ_j ‖Q_F a_j‖₂^p` for every `F` with `dim F ≤ k` and every `i`; and with
`S = Σ_i s_i`, `q_i = s_i/S`: `S ≤ 2D`, `q_i ≥ w_i/(2D)` and `q_i ≥ ρ_i/2`. -/
theorem lemma_3_2 :
    ∀ p : ℝ, 1 ≤ p → p < 2 → ∀ Γ : ℝ, 1 ≤ Γ →
    ∃ C : ℝ, ∀ (n d k : ℕ), 1 ≤ k →
    ∀ (A B E : Matrix (Fin n) (Fin d) ℝ), A = B + E →
    ∀ R : ℝ, R = ∑ i, norm2 (E i) ^ p → R ≤ Γ * OPT p k A → 0 < R →
    ∀ w : Fin n → ℝ, IsLewisWeights p B w →
      let D : ℝ := (k : ℝ) + B.rank
      let ρ : Fin n → ℝ := fun i => norm2 (E i) ^ p / R
      let s : Fin n → ℝ := fun i => w i + D * ρ i
      (∀ F : Submodule ℝ (EuclideanSpace ℝ (Fin d)), InFk k F → ∀ i : Fin n,
        ‖resid F (rowVec A i)‖ ^ p ≤ C * s i * ∑ j, ‖resid F (rowVec A j)‖ ^ p) ∧
      (∑ i, s i ≤ 2 * D) ∧
      (∀ i, w i / (2 * D) ≤ s i / ∑ j, s j) ∧
      (∀ i, ρ i / 2 ≤ s i / ∑ j, s j) := by sorry

end LpSubspaceCoreset.SmallP
