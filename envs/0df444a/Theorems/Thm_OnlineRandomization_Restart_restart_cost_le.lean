-- Prove2me | Theorems.Thm_OnlineRandomization_Restart_restart_cost_le
-- name    : OnlineRandomization.Restart.restart_cost_le
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T08:36:43.29399+00:00
-- url     : https://prove2.me/theorems/fcc20d9b-3375-4b43-a053-b3d15ca2b359
-- title:
--   Proof of Theorem 4.1, p. 18 — the restart algorithm costs at most $\alpha(c(1)) + \sum_{i=2}^{t} (\alpha(c(i)) + D(F))$
-- statement:
--   Let $F$ be a request-answer game with finite nonempty answer set, let $D$ bound its diameter, and let $H$ be a real number with $f_0 \le H$. Let $\alpha : \mathbb{R} \to \mathbb{R}$, and let $A_H$ be a deterministic online algorithm that is $\alpha$-competitive on $R_H$: $c_{A_H}(r) \le \alpha(c(r))$ for every $r \in R_H$. Then for every nonempty request sequence $r$ with restart segments $r(1), \dots, r(t)$ and $c(i) = c(r(i))$, the restart algorithm built from $A_H$ satisfies
--
--   $$c_{\mathrm{Restart}}(r) \le \alpha(c(1)) + \sum_{i=2}^{t} \big(\alpha(c(i)) + D\big).$$
--
--   The algorithm pays at most what $A_H$ pays on each segment, plus at most $D$ at each of the $t-1$ restarts. This is the upper bound on the algorithm's cost in the proof of Theorem 4.1.
--
--   **Formalization Note** Written as $\sum_{i=1}^t \alpha(c(i)) + (t-1) D$ with $t$ cast to a real number, which equals the page's expression for $t \ge 1$; hence the hypothesis $r \ne \emptyset$ (for $r = \emptyset$, $t = 0$ and the sum form would be false). "$\alpha$-competitive against any adaptive off-line adversary restricted to request sequences from $R_H$" is, for a deterministic algorithm, the stated inequality on every $r \in R_H$. The hypothesis $f_0 \le H$ makes every segment lie in $R_H$ (see `segments_greedy`); in Theorem 4.1 it follows from $f_0 \ge 0$ and $D \le H$. $\alpha$ is an arbitrary function here; no linearity is needed for this step.
-- source:
--   Ben-David, Borodin, Karp, Tardos and Wigderson, On the power of randomization in on-line algorithms, Algorithmica 11 (1994), manuscript p. 18, §4, proof of Theorem 4.1, fourth paragraph, sentence 1

import Mathlib
import Definitions.Def_OnlineRandomization_Restart_Model
import Definitions.Def_OnlineRandomization_Restart_GameProperties
import Definitions.Def_OnlineRandomization_Restart_RestartAlgorithm

namespace OnlineRandomization.Restart

/-- p. 18: if `D` bounds the diameter, `f_0 ≤ H`, and `A_H` is `α`-competitive on `R_H`, then
on every nonempty `r` with segments `r(1), …, r(t)` the restart algorithm costs at most
`α(c(1)) + Σ_{i=2}^{t} (α(c(i)) + D)`. -/
theorem restart_cost_le {R A : Type*} [Fintype A] [Nonempty A] (F : Game R A) (D H : ℝ)
    (hD : DiameterBound F D) (hf0 : F.cost [] [] ≤ H) (α : ℝ → ℝ) (AH : DetAlg R A)
    (hAH : ∀ r : List R, InRH F H r → AH.costOn F r ≤ α (F.opt r))
    (r : List R) (hr : r ≠ []) :
    (restart F H AH).costOn F r ≤
      ((segments F H r).map (fun s => α (F.opt s))).sum
        + (((segments F H r).length : ℝ) - 1) * D := by sorry

end OnlineRandomization.Restart
