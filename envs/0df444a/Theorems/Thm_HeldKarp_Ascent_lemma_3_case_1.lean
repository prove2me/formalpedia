-- Prove2me | Theorems.Thm_HeldKarp_Ascent_lemma_3_case_1
-- name    : HeldKarp.Ascent.lemma_3_case_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T06:50:10.50806+00:00
-- url     : https://prove2.me/theorems/c2899f9a-abf9-485e-be91-0747bca51bcd
-- title:
--   Lemma 3, Case 1: with $0<\varepsilon<\lambda_m\le 2$ the relaxation iterates enter $P_{\bar w}$ or converge to its boundary
-- statement:
--   Let $n \ge 3$, let $(c_{ij})$ be symmetric real edge weights on $K_n$, let $w$ be the 1-tree bound, and let $\|\cdot\|$ be the Euclidean norm. Fix a target value $\bar w < \max_\pi w(\pi)$, and let $P_{\bar w} = \{\pi : \bar w \le c_k + \pi\cdot v_k \text{ for all 1-trees } k\}$. Let $(\pi^m)_{m\ge 0}$ be generated from an arbitrary $\pi^0$ by
--   $$\pi^{m+1} = \pi^m + \lambda_m\,\frac{\bar w - w(\pi^m)}{\|v_{k(\pi^m)}\|^2}\,v_{k(\pi^m)}, \tag{6}$$
--   where $k(\pi^m)$ is a minimum-weight 1-tree at $\pi^m$. If there is $\varepsilon$ with
--   $$0 < \varepsilon < \lambda_m \le 2 \quad \text{for all } m,$$
--   then either some $\pi^l$ lies in $P_{\bar w}$, or $(\pi^m)$ converges to a point on the boundary of $P_{\bar w}$.
--
--   This is the convergence statement for the relaxation method with the "maximum residual" rule applied to the system (5); Theorem 1 is derived from it by a suitable choice of $\bar w$.
--
--   **Formalization Note** "$\bar w < \max_\pi w(\pi)$" is written as the existence of some $\pi$ with $\bar w < w(\pi)$ (equivalent, since the maximum is attained). A zero denominator in (6) gives a zero step in Lean; that happens only at a maximizer of $w$, which already lies in $P_{\bar w}$. The minimum-weight 1-tree may be chosen arbitrarily among ties at every step. The boundary is the topological frontier in $\mathbb R^n$. $n \ge 3$ is implicit in the paper.
-- source:
--   Held & Karp, The traveling-salesman problem and minimum spanning trees: Part II, Math. Programming 1 (1971), DOI 10.1007/BF01584070, §2, p. 11 (PDF p. 6), Lemma 3, Eq. (6), Case 1; proof p. 12 (PDF p. 7)

import Mathlib
import Definitions.Def_HeldKarp_Ascent_IsOneTree
import Definitions.Def_HeldKarp_Ascent_oneTreeBound

open Filter Topology

namespace HeldKarp.Ascent

/-- **Lemma 3, Case 1** — Held & Karp, *The traveling-salesman problem and minimum spanning trees:
Part II*, Math. Programming 1 (1971), §2, p. 11 (PDF p. 6); proof p. 12 (PDF p. 7):
"We assume that w̄ < max_π w(π). Let {π^m} be a sequence of points obtained by the process
π^{m+1} = π^m + λ_m ((w̄ − w(π^m)) / ‖v_{k(π^m)}‖²) v_{k(π^m)}   (6). […] Case 1: If, for some
ε, 0 < ε < λ_m ≤ 2 for all m, then {π^m} either includes a point π^l ∈ P_w̄ or converges to a point
on the boundary of P_w̄."

The sequence `π m` together with the 1-trees `T m` (the paper's `k(π^m)`) satisfies (6), each
`T m` being a minimum-weight 1-tree at `π m`.

Formalization Note: "w̄ < max_π w(π)" is written `∃ π, w̄ < w(π)` (equivalent, since `w` attains
its maximum). `‖·‖` is the Euclidean norm, written as a sum of squares. When
`‖v_{k(π^m)}‖² = 0` Lean's division gives step `0`; this happens only at a maximizer of `w`,
which already lies in `P_w̄`, so the left disjunct holds. After some `π^l` enters `P_w̄` the
formula (6) still determines the later points; no stopping rule is needed. Ties among
minimum-weight 1-trees may be broken arbitrarily at every step. The boundary is the topological
frontier in `Fin n → ℝ` (product topology = Euclidean topology). `3 ≤ n` is implicit in the
paper. -/
theorem lemma_3_case_1 {n : ℕ} [NeZero n] (hn : 3 ≤ n) (c : Sym2 (Fin n) → ℝ) (wbar : ℝ)
    (hwbar : ∃ π' : Fin n → ℝ, wbar < oneTreeBound c π')
    (π : ℕ → Fin n → ℝ) (T : ℕ → SimpleGraph (Fin n)) (hT : ∀ m, IsMinOneTree c (π m) (T m))
    (lam : ℕ → ℝ)
    (hstep : ∀ m, π (m + 1) = π m + (lam m * ((wbar - oneTreeBound c (π m)) /
      ∑ i, (degExcess (T m) i) ^ 2)) • degExcess (T m))
    (ε : ℝ) (hε : 0 < ε) (hlam : ∀ m, ε < lam m ∧ lam m ≤ 2) :
    (∃ l, π l ∈ feasibleSet c wbar) ∨
      ∃ p : Fin n → ℝ, Tendsto π atTop (𝓝 p) ∧ p ∈ frontier (feasibleSet c wbar) := by sorry

end HeldKarp.Ascent
