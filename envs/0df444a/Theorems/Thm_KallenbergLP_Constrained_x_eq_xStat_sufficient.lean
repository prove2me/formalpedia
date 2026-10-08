-- Prove2me | Theorems.Thm_KallenbergLP_Constrained_x_eq_xStat_sufficient
-- name    : KallenbergLP.Constrained.x_eq_xStat_sufficient
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:14:23.65964+00:00
-- url     : https://prove2.me/theorems/f4d59ece-c401-496c-a0ba-953694fceb6e
-- title:
--   Theorem 4.7.5 — two sufficient conditions for x* = x(π*)
-- statement:
--   Let $(x^*,y^*)$ be an optimal solution of the linear program (4.7.12) and let $\pi^*$ be a stationary decision rule given by (4.7.14). Then $x^*=x(\pi^*)$, where $x_{ja}(\pi)=[\beta^TP^*(\pi)]_j\pi_{ja}$, in each of the following cases:
--
--   1. the Markov chain with transition matrix $P(\pi^*)$ has one ergodic set plus a (perhaps empty) set of transient states;
--   2. $y^*_{ia}/\sum_ay^*_{ia}=\pi^*_{ia}$ for all $a\in A(i)$ and $i\in E_{x^*}\cap E_{y^*}$.
--
--   Together with Theorem 4.7.4 these conditions let one certify a stationary optimal policy for the constrained problem without computing $P^*(\pi^*)$.
--
--   **Formalization Note** "One ergodic set plus transient states" is the platform predicate `IsUnichainMatrix`: any two recurrent states (states lying in a closed communicating class) are mutually accessible.
-- source:
--   Kallenberg, Linear Programming and Finite Markovian Control Problems, Mathematical Centre Tracts 148, Mathematisch Centrum, Amsterdam 1983, p. 144, (4.7.14); p. 145, Theorem 4.7.5

import Mathlib
import Definitions.Def_MarkovDecisionProcesses_AverageReward
import Definitions.Def_KallenbergLP_Constrained_Frequencies
import Definitions.Def_KallenbergLP_Constrained_Problem

namespace KallenbergLP.Constrained

open MarkovDecisionProcesses

/-- Kallenberg (1983), Theorem 4.7.5, p. 145: for an optimal solution `(x*, y*)` of (4.7.12) and
`π*` given by (4.7.14), `x* = x(π*)` holds (i) if the Markov chain under `P(π*)` has one ergodic
set plus a (perhaps empty) set of transient states, and (ii) if
`y*_{ia} / ∑_a y*_{ia} = π*_{ia}` for `a ∈ A(i)`, `i ∈ E_{x*} ∩ E_{y*}`. -/
theorem x_eq_xStat_sufficient {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S]
    [DecidableEq A] (M : StationaryMDP S A) (β : S → ℝ) (hβ0 : ∀ j, 0 ≤ β j)
    (hβ1 : ∑ j, β j = 1) {m : ℕ} (q : KallenbergLP.AverageLP.Pair M → Fin m → ℝ) (b : Fin m → ℝ)
    (x y : KallenbergLP.AverageLP.Pair M → ℝ) (hopt : Optimal476 M β q b x y)
    (π : KallenbergLP.AverageLP.Pair M → ℝ) (hπ : π ∈ StatRule M) (h4714 : IsRule4714 x y π) :
    (IsUnichainMatrix (policyMatrix π) → x = xStat β π) ∧
    ((∀ p : KallenbergLP.AverageLP.Pair M, 0 < stateMass x p.1.1 → 0 < stateMass y p.1.1 →
        y p / stateMass y p.1.1 = π p) → x = xStat β π) := by sorry

end KallenbergLP.Constrained
