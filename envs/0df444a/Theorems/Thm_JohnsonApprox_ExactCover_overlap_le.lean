-- Prove2me | Theorems.Thm_JohnsonApprox_ExactCover_overlap_le
-- name    : JohnsonApprox.ExactCover.overlap_le
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T15:33:27.125738+00:00
-- url     : https://prove2.me/theorems/ba647b73-98fa-4778-9e8f-d0c00b7ccfea
-- title:
--   Proof of Theorem 6 — the cumulative overlap is at most |T|(a[ln(k) + 1] − 1)
-- statement:
--   Let $k \ge 1$ and let $F$ be an input of EC$(k)$ (every set has at most $k$ points) whose covered set $T$ is nonempty. Write $F^* = a|T|$. For every halting run of algorithm C2 on $F$, with returned subcover $F_1$, the cumulative overlap satisfies
--   $$\mathrm{OV}(F_1) \le |T|\big(a[\ln(k) + 1] - 1\big).$$
--
--   Together with $m_{EC}(F_1) = |T| + \mathrm{OV}(F_1)$ this gives $m_{EC}(F_1) \le a|T|[\ln(k)+1] = F^*[\ln(k)+1]$, the upper bound of Theorem 6.
--
--   **Formalization Note** The run and its cumulative overlap are `RunOV F σ v` with `σ` halting; $a = F^*/|T|$ as a real number, and $\ln$ is `Real.log`. The hypothesis $T \neq \emptyset$ makes $a$ defined; the case $T = \emptyset$ is trivial for the theorem.
-- source:
--   Johnson, Approximation algorithms for combinatorial problems, J. Comput. System Sci. 9 (1974), p. 272, proof of Theorem 6

import Mathlib
import Definitions.Def_JohnsonApprox_ExactCover_Problem
import Definitions.Def_JohnsonApprox_ExactCover_C2

namespace JohnsonApprox.ExactCover

/-- Proof of Theorem 6 (p. 272): on an input of `EC(k)` with `T ≠ ∅` and `a = F*/|T|`, every
halting run of C2 has cumulative overlap `OV(F₁) ≤ |T|(a[ln(k) + 1] − 1)`. -/
theorem overlap_le {α : Type} [DecidableEq α] (k : ℕ) (hk : 1 ≤ k) (F : Input α)
    (hF : InEC k F) (hT : F.ground.Nonempty) {σ : State F} {ov : ℕ}
    (hrun : RunOV F σ ov) (hσ : Halts σ) :
    (ov : ℝ) ≤ (F.ground.card : ℝ) *
      (((F.opt : ℝ) / (F.ground.card : ℝ)) * (Real.log k + 1) - 1) := by sorry

end JohnsonApprox.ExactCover
