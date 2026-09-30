-- Prove2me | Theorems.Thm_HeldKarp_Ascent_lemma_3_case_2
-- name    : HeldKarp.Ascent.lemma_3_case_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T06:59:19.203707+00:00
-- url     : https://prove2.me/theorems/c62dc5be-f6d4-45df-abcc-0e8a4df9c633
-- title:
--   Lemma 3, Case 2: with $\lambda_m = 2$ the relaxation iterates reach $P_{\bar w}$
-- statement:
--   Let $n \ge 3$, let $(c_{ij})$ be symmetric real edge weights on $K_n$, let $w$ be the 1-tree bound, and let $\|\cdot\|$ be the Euclidean norm. Fix a target value $\bar w < \max_\pi w(\pi)$ and let $P_{\bar w}$ be the polyhedron of solutions of the system $\bar w \le c_k + \pi\cdot v_k$ over all 1-trees $k$. Let $(\pi^m)$ be generated from an arbitrary $\pi^0$ by
--   $$\pi^{m+1} = \pi^m + 2\,\frac{\bar w - w(\pi^m)}{\|v_{k(\pi^m)}\|^2}\,v_{k(\pi^m)},$$
--   that is, by (6) with $\lambda_m = 2$ for all $m$, where $k(\pi^m)$ is a minimum-weight 1-tree at $\pi^m$. Then some iterate lies in $P_{\bar w}$:
--   $$\exists\, l:\ \pi^l \in P_{\bar w}.$$
--
--   With $\lambda_m = 2$ each step reflects the current point in the hyperplane of a most-violated inequality of (5); the lemma says that finitely many reflections reach the target polyhedron. The paper obtains this case from Case 2 of Theorem 1 of Motzkin and Schoenberg [12].
--
--   **Formalization Note** "$\bar w < \max_\pi w(\pi)$" is written as the existence of some $\pi$ with $\bar w < w(\pi)$. A zero denominator gives a zero step in Lean, which happens only at a maximizer of $w$, a point of $P_{\bar w}$. Ties among minimum-weight 1-trees may be broken arbitrarily. $n \ge 3$ is implicit in the paper.
-- source:
--   Held & Karp, The traveling-salesman problem and minimum spanning trees: Part II, Math. Programming 1 (1971), DOI 10.1007/BF01584070, §2, pp. 11–12 (PDF pp. 6–7), Lemma 3, Eq. (6), Case 2

import Mathlib
import Definitions.Def_HeldKarp_Ascent_IsOneTree
import Definitions.Def_HeldKarp_Ascent_oneTreeBound

namespace HeldKarp.Ascent

/-- **Lemma 3, Case 2** — Held & Karp, *The traveling-salesman problem and minimum spanning trees:
Part II*, Math. Programming 1 (1971), §2, pp. 11–12 (PDF pp. 6–7): "We assume that
w̄ < max_π w(π). Let {π^m} be a sequence of points obtained by the process
π^{m+1} = π^m + λ_m ((w̄ − w(π^m)) / ‖v_{k(π^m)}‖²) v_{k(π^m)}   (6). […] Case 2. If λ_m = 2 for
all m, then the sequences {π^m} always includes a point π^l ∈ P_w̄."

The sequence `π m` together with the 1-trees `T m` (the paper's `k(π^m)`) satisfies (6) with
`λ_m = 2`, each `T m` being a minimum-weight 1-tree at `π m`.

Formalization Note: "w̄ < max_π w(π)" is written `∃ π, w̄ < w(π)` (equivalent, since `w` attains
its maximum). `‖·‖` is the Euclidean norm, written as a sum of squares; a zero denominator gives
step `0` in Lean, which happens only at a maximizer of `w`, already a point of `P_w̄`. Ties
among minimum-weight 1-trees may be broken arbitrarily at every step. The paper proves this case
by citing Case 2 of Theorem 1 of its reference [12] (Motzkin–Schoenberg). `3 ≤ n` is implicit in
the paper. -/
theorem lemma_3_case_2 {n : ℕ} [NeZero n] (hn : 3 ≤ n) (c : Sym2 (Fin n) → ℝ) (wbar : ℝ)
    (hwbar : ∃ π' : Fin n → ℝ, wbar < oneTreeBound c π')
    (π : ℕ → Fin n → ℝ) (T : ℕ → SimpleGraph (Fin n)) (hT : ∀ m, IsMinOneTree c (π m) (T m))
    (hstep : ∀ m, π (m + 1) = π m + (2 * ((wbar - oneTreeBound c (π m)) /
      ∑ i, (degExcess (T m) i) ^ 2)) • degExcess (T m)) :
    ∃ l, π l ∈ feasibleSet c wbar := by sorry

end HeldKarp.Ascent
