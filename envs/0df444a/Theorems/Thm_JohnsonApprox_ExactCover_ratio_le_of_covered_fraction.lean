-- Prove2me | Theorems.Thm_JohnsonApprox_ExactCover_ratio_le_of_covered_fraction
-- name    : JohnsonApprox.ExactCover.ratio_le_of_covered_fraction
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T15:32:36.586851+00:00
-- url     : https://prove2.me/theorems/5d3cf45c-f40a-44b4-8b4a-eb608acfa096
-- title:
--   Proof of Theorem 6 — the next chosen set has Ratio(S′) ≤ a/(1 − x) − 1
-- statement:
--   Let $F$ be an input of SET COVERING II with nonempty covered set $T$ and optimum $F^* = a|T|$. At a state reachable by algorithm C2 on $F$, let
--   $$x = \frac{|T - \mathrm{UNCOV}|}{|T|}$$
--   be the fraction of $T$ covered so far. If C2 may choose $S'$ next, then
--   $$\mathrm{Ratio}(S') = \frac{|S' - \mathrm{UNCOV}|}{|S' \cap \mathrm{UNCOV}|} \le \frac{a}{1-x} - 1.$$
--
--   This bounds the overlap paid per newly covered point by an increasing function of the covered fraction; integrating it gives the bound on the cumulative overlap.
--
--   **Formalization Note** Every denominator is positive: $|T| > 0$ by hypothesis, a set C2 may choose meets UNCOV, and UNCOV $\neq \emptyset$ whenever C2 may choose, so $1 - x = |\mathrm{UNCOV}|/|T| > 0$. Here $a = F^*/|T|$ as a real number.
-- source:
--   Johnson, Approximation algorithms for combinatorial problems, J. Comput. System Sci. 9 (1974), p. 271, proof of Theorem 6

import Mathlib
import Definitions.Def_JohnsonApprox_ExactCover_Problem
import Definitions.Def_JohnsonApprox_ExactCover_C2

namespace JohnsonApprox.ExactCover

/-- Proof of Theorem 6 (p. 271): with `a = F*/|T|` and `x = |T − UNCOV|/|T|`, the next set `S′`
chosen by C2 has `Ratio(S′) ≤ a/(1 − x) − 1`. -/
theorem ratio_le_of_covered_fraction {α : Type} [DecidableEq α] (F : Input α)
    (hT : F.ground.Nonempty) {σ : State F} {i : Fin F.p} (hσ : Reachable F σ)
    (hi : MayChoose F σ i) :
    ((F.S i \ σ.UNCOV).card : ℝ) / ((F.S i ∩ σ.UNCOV).card : ℝ) ≤
      ((F.opt : ℝ) / (F.ground.card : ℝ)) /
        (1 - ((F.ground \ σ.UNCOV).card : ℝ) / (F.ground.card : ℝ)) - 1 := by sorry

end JohnsonApprox.ExactCover
