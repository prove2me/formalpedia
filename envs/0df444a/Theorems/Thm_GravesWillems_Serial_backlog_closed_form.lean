-- Prove2me | Theorems.Thm_GravesWillems_Serial_backlog_closed_form
-- name    : GravesWillems.Serial.backlog_closed_form
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-26T21:17:29.946318+00:00
-- url     : https://prove2.me/theorems/5b0c9a09-ccc7-4df7-b01e-2f97d2d18b2f
-- title:
--   Eq. (A2) — closed max-form of the backlog $Q_i(t)$
-- statement:
--   Let $Q_i(t)$ be the backlog of the $N$-stage serial base-stock system defined by the recursion (A1), with lead times $T_i \in \mathbb{N}$, arbitrary real base stocks $B_i$ and an arbitrary real demand path $d$. Then for every stage $i \in \{1, \dots, N\}$ and every period $t \in \mathbb{Z}$,
--   $$Q_i(t) = \max\Bigl[0,\; \max_{i \le j \le N} \bigl( d(t - T_i - T_{i+1} - \dots - T_j,\, t] - B_i - B_{i+1} - \dots - B_j \bigr)\Bigr].$$
--
--   That is, the backlog at stage $i$ is the largest excess of demand over a window reaching back through the lead times of stages $i, \dots, j$ over the base stocks held at those stages. This closed form is what makes the expected backlogs tractable as functions of the base stocks.
--
--   **Formalization Note** The inner maximum is `Finset.sup'` over the nonempty range $\{i, \dots, N\}$; no hypothesis on the signs of $B$ or $d$ is needed.
-- source:
--   Graves and Willems, Optimizing Strategic Safety Stock Placement in Supply Chains, Manufacturing & Service Operations Management 2(1), 2000, p. 81, Appendix, Eq. (A2)

import Mathlib
import Definitions.Def_GravesWillems_Serial_backlog

namespace GravesWillems.Serial

/-- Eq. (A2) of Graves–Willems 2000 (Appendix, p. 81): the backlog defined by the recursion (A1)
has the closed max-form
`Qᵢ(t) = max[0, max_{i ≤ j ≤ N} (d(t − Tᵢ − ⋯ − T_j, t] − Bᵢ − ⋯ − B_j)]` for `i = 1, …, N`. -/
theorem backlog_closed_form (N : ℕ) (T : ℕ → ℕ) (B : ℕ → ℝ) (d : ℤ → ℝ) (i : ℕ)
    (hi : i ∈ Finset.Icc 1 N) (t : ℤ) :
    backlog N T B d i t =
      max 0 ((Finset.Icc i N).sup' (Finset.nonempty_Icc.mpr (Finset.mem_Icc.mp hi).2)
        (fun j => windowDemand d (t - ((∑ m ∈ Finset.Icc i j, T m : ℕ) : ℤ)) t
          - ∑ m ∈ Finset.Icc i j, B m)) := by sorry

end GravesWillems.Serial
