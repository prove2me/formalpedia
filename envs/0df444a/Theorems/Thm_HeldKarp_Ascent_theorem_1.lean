-- Prove2me | Theorems.Thm_HeldKarp_Ascent_theorem_1
-- name    : HeldKarp.Ascent.theorem_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T07:16:51.939205+00:00
-- url     : https://prove2.me/theorems/4f3eecf9-a1b3-4522-948b-2c9e150131c9
-- title:
--   Theorem 1: the constant-step ascent satisfies $\sup_m w(\pi^m) \ge \max_\pi w(\pi) - \tfrac12\bar t\,\limsup_m \|v_{k(\pi^m)}\|^2$
-- statement:
--   Let $n \ge 3$, let $(c_{ij})$ be arbitrary symmetric real edge weights on the complete graph $K_n$, and let $w(\pi) = \min_k [c_k + \pi\cdot v_k]$ be the 1-tree bound, where $k$ ranges over the 1-trees, $c_k$ is the weight of the $k$-th 1-tree and $v_k$ its degree-excess vector ($d_{ik} - 2$ in coordinate $i$). Let $\|\cdot\|$ be the Euclidean norm. Fix a step size $\bar t > 0$ and a starting point $\pi^0 \in \mathbb R^n$, and run the iteration (3) with constant step $t_m = \bar t$:
--   $$\pi^{m+1} = \pi^m + \bar t\, v_{k(\pi^m)},$$
--   where $k(\pi^m)$ is a minimum-weight 1-tree at the point $\pi^m$ (ties broken arbitrarily). Then
--   $$\sup_m w(\pi^m) \;\ge\; \max_\pi w(\pi) - \tfrac12\,\bar t\,\limsup_{m\to\infty}\|v_{k(\pi^m)}\|^2.$$
--
--   The theorem quantifies how close the simple constant-step ascent used in the paper's computations gets to the Held–Karp bound $\max_\pi w(\pi)$: the gap is governed by the step size and by how far the 1-trees produced asymptotically are from being tours ($\|v_k\|^2 = 0$ exactly when the 1-tree is a tour).
--
--   **Formalization Note** The conclusion is stated in the equivalent form: for every $\pi^*$ and every $\delta > 0$ there is $m$ with $w(\pi^*) - \tfrac12\bar t L - \delta < w(\pi^m)$, where $L = \limsup_m \|v_{k(\pi^m)}\|^2$. This avoids naming the maximizer and avoids a supremum of a possibly unbounded family. $L$ is the limit superior of a sequence taking finitely many values, hence a real number. The 1-tree chosen at each step may be any minimum-weight 1-tree. The hypotheses $\bar t > 0$ and $n \ge 3$ are implicit in the paper.
-- source:
--   Held & Karp, The traveling-salesman problem and minimum spanning trees: Part II, Math. Programming 1 (1971), DOI 10.1007/BF01584070, §2, p. 12 (PDF p. 7), Theorem 1 (iteration (3), p. 8–9); proof pp. 13–14 (PDF pp. 8–9)

import Mathlib
import Definitions.Def_HeldKarp_Ascent_IsOneTree
import Definitions.Def_HeldKarp_Ascent_oneTreeBound

open Filter

namespace HeldKarp.Ascent

/-- **Theorem 1** — Held & Karp, *The traveling-salesman problem and minimum spanning trees:
Part II*, Math. Programming 1 (1971), §2, p. 12 (PDF p. 7); proof pp. 13–14 (PDF pp. 8–9):
"The iteration (3), with t_m = t̄ for all m, satisfies:
sup_m w(π^m) ≥ max_π w(π) − ½ t̄ lim sup_{m→∞} ‖v_{k(π^m)}‖²."
The iteration (3) is `π^{m+1} = π^m + t_m v_{k(π^m)}`, where `k(π)` is the index of a
minimum-weight 1-tree at the point `π`.

Here `π 0` is an arbitrary starting point, `T m` is a minimum-weight 1-tree at `π m` (the
paper's `k(π^m)`) and `π (m+1) = π m + t̄ • v_{T m}`. With
`L = lim sup_m ‖v_{T m}‖²`, the conclusion says: for every point `π*` and every `δ > 0` some
iterate has `w(π^m) > w(π*) − ½ t̄ L − δ`.

Formalization Note: the paper's inequality is stated in the equivalent form
"for all `π*`, `δ > 0` there is `m` with `w(π*) − t̄/2 · L − δ < w(π^m)`", which says
`sup_m w(π^m) ≥ w(π*) − ½ t̄ L` for every `π*`, i.e. `≥ max_π w(π) − ½ t̄ L`; this form needs no
existence of the maximum and no `⨆` of a possibly unbounded family. `‖·‖` is the Euclidean norm
(footnote, p. 9), written as a sum of squares. `L` is `Filter.limsup` of a sequence taking
finitely many values (degree vectors of graphs on `Fin n`), hence a genuine real. Ties among
minimum-weight 1-trees may be broken arbitrarily, and differently at every step. `0 < t̄` and
`3 ≤ n` are implicit in the paper (`t̄ = 0` makes the statement false). -/
theorem theorem_1 {n : ℕ} [NeZero n] (hn : 3 ≤ n) (c : Sym2 (Fin n) → ℝ) (tbar : ℝ)
    (htbar : 0 < tbar) (π : ℕ → Fin n → ℝ) (T : ℕ → SimpleGraph (Fin n))
    (hT : ∀ m, IsMinOneTree c (π m) (T m))
    (hstep : ∀ m, π (m + 1) = π m + tbar • degExcess (T m)) :
    ∀ πstar : Fin n → ℝ, ∀ δ : ℝ, 0 < δ → ∃ m : ℕ,
      oneTreeBound c πstar
          - tbar / 2 * limsup (fun m => ∑ i, (degExcess (T m) i) ^ 2) atTop - δ
        < oneTreeBound c (π m) := by sorry

end HeldKarp.Ascent
