-- Prove2me | Theorems.Thm_Fundraising_PartialCollab_eq_S11
-- name    : Fundraising.PartialCollab.eq_S11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-16T08:03:16.41824+00:00
-- url     : https://prove2.me/theorems/caa3497e-5250-488a-b9d5-25c7f0da942b
-- title:
--   (S11), proof of Proposition 4, p. S13 — equilibria are exactly profiles where each HO maximizes δ_iθ^p_i and x_i = (α^p_i − Σ_{j≠i} x_j)^+
-- statement:
--   Consider the partial-collaboration game under its standing hypotheses, and let $(s, x)$ be a profile with $s_i \in [a_i, b_i]$ and $x_i \in [0, 1]$ for every HO $i$. Write $\alpha^p_i(s) = \min\left(B_i / (\delta_i(s_i)\theta^p_i(s)), 1\right)$.
--
--   Then $(s, x)$ is a Nash equilibrium if and only if, for every HO $i$,
--   1. $s_i$ maximizes the performance per contacted donor over HO $i$'s interval, the other base utilities being fixed:
--   $$s_i \in \arg\max_{\sigma \in [a_i, b_i]} \delta_i(\sigma)\, \theta^p_i(\sigma, s_{-i});$$
--   2. HO $i$'s effort tops up the others' effort exactly to $\alpha^p_i(s)$:
--   $$x_i = \Big(\alpha^p_i(s) - \sum_{j \ne i} x_j\Big)^+ .$$
--
--   This is the bridge between the lexicographic equilibrium definition and the two decoupled conditions from which both parts of Proposition 4 follow: the base-utility condition becomes the KKT system (11), and the effort conditions form the system solved in part (ii).
--
--   **Formalization Note** The maximization is stated as `IsMaxOn` on $[a_i, b_i]$; $(\cdot)^+$ is `max (·) 0`. The paper's (S11) is a joint maximization over $(s_i, x_i)$ subject to the effort equation; since the objective does not depend on $x_i$ and the equation determines $x_i \in [0,1]$ from $s$, the two readings agree.
-- source:
--   Aflaki, Pedraza-Martinez, Competition and Collaboration on Fundraising for Short-Term Disaster Response: The Impact on Earmarking and Performance, SSRN 3705595 (version of December 2022), p. S13 (PDF 46), proof of Proposition 4, display (S11)

import Mathlib
import Definitions.Def_Fundraising_PartialCollab_Setting

namespace Fundraising.PartialCollab

open Finset

/-- (S11), proof of Proposition 4, p. S13: a profile in the strategy box is a Nash equilibrium of
the partial-collaboration game iff, for every HO `i`, `s_i` maximizes `σ ↦ δ_i(σ) θ^p_i(σ, s_{-i})`
on `[a_i, b_i]` and `x_i = (α^p_i(s) − Σ_{j ≠ i} x_j)^+`. -/
theorem eq_S11 {n : ℕ} (G : Setting n) (hG : G.Standing) (s x : Fin n → ℝ)
    (hbox : G.InBox s x) :
    G.IsNE s x ↔ ∀ i : Fin n,
      IsMaxOn (fun t => G.δ i t * theta (Function.update s i t) i)
        (Set.Icc (G.a i) (G.b i)) (s i) ∧
      x i = max (G.alpha s i - ∑ j ∈ univ.erase i, x j) 0 := by sorry

end Fundraising.PartialCollab
