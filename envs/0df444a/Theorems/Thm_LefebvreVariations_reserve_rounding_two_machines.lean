-- Prove2me | Theorems.Thm_LefebvreVariations_reserve_rounding_two_machines
-- name    : LefebvreVariations.reserve_rounding_two_machines
-- status  : Open
-- author  : @Secousses
-- created : 2026-11-26T22:18:26.392703+00:00
-- url     : https://prove2.me/theorems/43c256a1-05cb-4969-a3a9-3d7e10dba729
-- title:
--   Lefebvre's variations, No. 249 — on a theme by Mahboub and Rahgoshay: rounding a fractional assignment to two machines costs at most one largest job
-- statement:
--   Let $n\ge0$, let $p_{ij}\ge0$ ($i\in\{1,2\}$, $j\le n$) be the processing time of job $j$ on machine $i$, and let $y_{ij}\ge0$ with $y_{1j}+y_{2j}=1$ for every job $j$. Put
--   $$
--   L_i=\sum_{j}p_{ij}y_{ij},\qquad q_i=\max\{p_{ij}:\ y_{ij}>0\}\quad(q_i=0\text{ if no such }j).
--   $$
--   Then there is an assignment $\pi:\{1,\dots,n\}\to\{1,2\}$ using only supported arcs, $y_{\pi(j)j}>0$ for all $j$, such that for each machine $i\in\{1,2\}$
--   $$
--   \sum_{j:\ \pi(j)=i}p_{ij}\ \le\ L_i+q_i .
--   $$
--
--   This is the two-machine case of the whole-job rounding lemma for fractional assignments (loads $L_i+q_i$), which the platform lists as open for every number $m$ of machines. For two machines the rounding is a threshold argument on the fractions $y_{1j}$.
--
--   **Formalization Note** The times and fractions are `p y : Fin 2 → Fin n → ℝ`; `q_i` is `⨆ j : {j // 0 < y i j}, p i j`, which is `0` for an empty support. All jobs `j : Fin n` are assigned, and $n=0$ is allowed.
--
--   **Why this is a variation.** A variation on the open platform problem ReserveLB.lemma_2_1 (whole-job rounding of a fractional assignment to loads at most L_i + q_i), played at m = 2 machines with the parent's statement restated verbatim at Fin 2, not imported. One machine is trivial; two machines is the first non-trivial size, and the lemma for all m stays open.
--
--   **Attribution.** This statement belongs to *Lefebvre's variations*, a series proposed by Erwan Lefebvre: each variation plays an open problem of the platform at its first non-trivial size, so that it can be settled and then reused to attack the open problem itself.
-- source:
--   D. B. Shmoys and E. Tardos, An approximation algorithm for the generalized assignment problem, Mathematical Programming 62 (1993) 461-474, and J. K. Lenstra, D. B. Shmoys, E. Tardos, Approximation algorithms for scheduling unrelated parallel machines, Mathematical Programming 46 (1990) (both cited from memory, page numbers not verified). The platform lemma is Lemma 2.1 of Mahboub and Rahgoshay, as quoted. Tested by exhaustive search over assignments on 20000 random instances with two machines and up to 7 jobs (no failure).

import Mathlib

set_option autoImplicit false

namespace LefebvreVariations

/-- The two-machine case (`m = 2`) of `ReserveLB.lemma_2_1` (whole-job rounding to loads `L_i + q_i`): for processing
times `p_ij ≥ 0` of `n` jobs on two machines and a fractional assignment `y ≥ 0` with `Σ_i y_ij = 1`, put
`L_i = Σ_j p_ij y_ij` and `q_i = max {p_ij : y_ij > 0}` (`0` if there is none). Then some whole-job assignment `π`
uses only arcs with `y_(π j) j > 0` and puts load at most `L_i + q_i` on each machine `i`.
Source: the rounding of Shmoys and Tardos, *An approximation algorithm for the generalized assignment problem*,
Math. Programming 62 (1993), and Lenstra–Shmoys–Tardos, Math. Programming 46 (1990) (both cited from memory). -/
theorem reserve_rounding_two_machines {n : ℕ} (p : Fin 2 → Fin n → ℝ) (hp : ∀ i j, 0 ≤ p i j)
    (y : Fin 2 → Fin n → ℝ) (hy : ∀ i j, 0 ≤ y i j) (hsum : ∀ j, ∑ i, y i j = 1) :
    ∃ π : Fin n → Fin 2, (∀ j, 0 < y (π j) j) ∧
      ∀ i, ∑ j ∈ Finset.univ.filter (fun j => π j = i), p i j ≤
        ∑ j, p i j * y i j + ⨆ j : {j : Fin n // 0 < y i j}, p i j.val := by
  sorry

end LefebvreVariations
