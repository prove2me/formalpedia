-- Prove2me | Theorems.Thm_GraphSimOT_Gaps_lemma_47
-- name    : GraphSimOT.Gaps.lemma_47
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T18:07:50.306372+00:00
-- url     : https://prove2.me/theorems/d9ae51ea-3882-4982-92dd-c21f03438b3d
-- title:
--   Lemma 47 — merging two permutations: ρ(P, (1−θ)P₀ + θP₁) ≤ 20Mn^{−1/3} (M = √2), for any vectors with ‖z_ij‖ ≤ √2
-- statement:
--   Let $n\ge2$ and let $z_{ij}\in\mathbb R^m$ ($i,j\in[n]$, $m\ge1$) be vectors with $\|z_{ij}\|\le M := \sqrt2$; let $\rho$ be the pseudometric of Eq. (34) defined by them: $\rho(Q,Q') = \sup_{\|w\|\le1}|h_Q(w) - h_{Q'}(w)|$, with $h_Q$ the support function of the zonotope $Z_Q = \{\frac1n\sum_{i,j}Q_{ij}a_{ij}z_{ij} : a_{ij}\in[0,1]\}$. Then for all permutation matrices $P_0, P_1$ and $\theta\in[0,1]$ there is a permutation matrix $P$ with
--   $$\rho\big(P,\ (1-\theta)P_0 + \theta P_1\big)\ \le\ 20\,M\,n^{-1/3}.$$
--
--   In the paper the vectors are those of Lemma 45 (for a fixed $t$, with $m\le 2n$); its proof "uses no property of the vectors $z_{ij}$ other than $\|z_{ij}\|\le M$". Merging along a binary tree (Lemma 48) gives Theorem 39.
--
--   Differences from the source:
--   - generalization: the vectors z_ij ∈ R^m fixed in App. E.2.2 from Lemma 45 (for a fixed t > 0, with m ≤ 2n), M := √2 → every m > 0 and every z : Fin n → Fin n → EuclideanSpace ℝ (Fin m) with ‖z i j‖ ≤ √2; reason: the proof uses only ‖z_ij‖ ≤ M (p. 41); the vectors of Lemma 45 satisfy this, so the statement specializes to the paper's
--   - encoding: h_Q(w) = max_{u ∈ Z_Q} ⟨w, u⟩ and ρ(Q, Q') = sup_{w ∈ B_H} |h_Q(w) − h_Q'(w)| → suppFn (sSup over the zonotope) and rhoZ (⨆ over the closed unit ball); reason: both sets are nonempty and bounded, so these are the paper's maximum and supremum
--   - encoding: indices in [n] = {1, …, n} → Fin n = {0, …, n − 1}; reason: relabelling of the index set; no instance changes
-- source:
--   Breitung, Gervens, Grohe, Graph Similarity Meets Optimal Transport, arXiv:2611.05048 (held version, sha256 1cd10e91…), p. 41, Lemma 47 (setting p. 40)

import Mathlib
import Definitions.Def_GraphSimOT_Gaps_CutRounding

namespace GraphSimOT.Gaps

/-- Lemma 47 (Merging Two Permutations, App. E.2.2, p. 41), with `M = √2`, stated for every
family of vectors `z_ij ∈ ℝ^m` with `‖z_ij‖ ≤ √2` (the only property of the vectors of
Lemma 45 the proof uses): for all permutation matrices `P_0, P_1` and `θ ∈ [0, 1]` there is a
permutation matrix `P` with `ρ(P, (1 − θ) P_0 + θ P_1) ≤ 20 M n^{-1/3}`. -/
theorem lemma_47 {n : ℕ} (hn : 2 ≤ n) {m : ℕ} (hm : 0 < m)
    (z : Fin n → Fin n → EuclideanSpace ℝ (Fin m)) (hz : ∀ i j, ‖z i j‖ ≤ Real.sqrt 2)
    (π₀ π₁ : Equiv.Perm (Fin n)) (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    ∃ π : Equiv.Perm (Fin n),
      rhoZ z (π.permMatrix ℝ) ((1 - θ) • π₀.permMatrix ℝ + θ • π₁.permMatrix ℝ)
        ≤ 20 * Real.sqrt 2 * (n : ℝ) ^ (-(1 / 3 : ℝ)) := by sorry

end GraphSimOT.Gaps
