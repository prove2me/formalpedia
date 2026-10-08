-- Prove2me | Theorems.Thm_KallenbergLP_AverageLP_theorem_4_2_1
-- name    : KallenbergLP.AverageLP.theorem_4_2_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T10:33:10.088683+00:00
-- url     : https://prove2.me/theorems/57a9bc4f-3853-467b-943d-6f643f9e1481
-- title:
--   Theorem 4.2.1 — a Blackwell optimal pure policy solves the pair of multichain optimality equations
-- statement:
--   Consider a finite Markov decision model with state set $E$, finite action sets $A(i)$, rewards $r_{ia}$ and transition probabilities $p_{iaj}$ with $\sum_jp_{iaj}=1$. Let $f_\circ^\infty$ be a pure and stationary policy that is Blackwell optimal, and put $\phi^\circ:=\phi(f_\circ^\infty)$, its average reward vector, and $u^\circ:=D(f_\circ)r(f_\circ)$, where $D(f_\circ)$ is the deviation matrix of $P(f_\circ)$. Then $(\tilde\phi,\tilde u)=(\phi^\circ,u^\circ)$ satisfies the pair of optimality equations
--   $$\tilde\phi_i=\max_{a\in A(i)}\sum_jp_{iaj}\tilde\phi_j,\qquad \tilde\phi_i+\tilde u_i=\max_{a\in\bar A(i)}\Big\{r_{ia}+\sum_jp_{iaj}\tilde u_j\Big\},\qquad i\in E,$$
--   where $\bar A(i):=\{a\in A(i)\mid\tilde\phi_i=\sum_jp_{iaj}\tilde\phi_j\}$.
--
--   These are the multichain average-reward optimality equations; no unichain assumption is made, which is why two equations are needed.
--
--   **Formalization Note** The second maximum is over the set $\bar A(i)$, whose nonemptiness is part of the conclusion. Blackwell optimality compares discounted rewards against all history-dependent randomized policies.
-- source:
--   Kallenberg, Linear Programming and Finite Markovian Control Problems, Mathematical Centre Tracts 148, Mathematisch Centrum, Amsterdam 1983, p. 97, Theorem 4.2.1

import Mathlib
import Definitions.Def_MarkovDecisionProcesses_AverageReward
import Definitions.Def_BlackwellDiscreteDP_NearOne_LimitMatrix
import Definitions.Def_KallenbergLP_AverageLP_Model
open MarkovDecisionProcesses BlackwellDiscreteDP.NearOne Matrix Filter

namespace KallenbergLP.AverageLP

variable {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S] [DecidableEq A]

/-- **Theorem 4.2.1.** Let `f₀^∞` be a Blackwell optimal pure and stationary policy. Then
`φ° := φ(f₀^∞)` and `u° := D(f₀)r(f₀)` satisfy the pair of optimality equations
(4.2.1) `φ̃_i = max_{a ∈ A(i)} Σ_j p_iaj φ̃_j`, `i ∈ E`, and
(4.2.2) `φ̃_i + ũ_i = max_{a ∈ Ā(i)} {r_ia + Σ_j p_iaj ũ_j}`, `i ∈ E`,
where `Ā(i) = {a ∈ A(i) | φ̃_i = Σ_j p_iaj φ̃_j}`.

Kallenberg, Linear Programming and Finite Markovian Control Problems, Mathematical Centre Tracts 148, Mathematisch Centrum, Amsterdam 1983, p. 97, Theorem 4.2.1.

**Formalization Note.** `φ(f₀^∞)` is the lim inf average reward of the pure stationary policy;
the maximum in (4.2.2) is over `Ā(i)`, whose nonemptiness is part of the conclusion. -/
theorem theorem_4_2_1 (M : StationaryMDP S A) (f₀ : S → A) (hf₀ : ∀ i, f₀ i ∈ M.admissible i)
    (hB : IsBlackwellOptimal M (stationaryPolicy M f₀ hf₀)) :
    let φ₀ : S → ℝ := fun i => gainInf (stationaryPolicy M f₀ hf₀) i
    let u₀ : S → ℝ := uPure M f₀
    (∀ i, φ₀ i = (M.admissible i).sup' (M.admissible_nonempty i)
        (fun a => ∑ j, M.trans i a j * φ₀ j)) ∧
    (∀ i, ∃ h : (Abar M φ₀ i).Nonempty, φ₀ i + u₀ i = (Abar M φ₀ i).sup' h
        (fun a => M.reward i a + ∑ j, M.trans i a j * u₀ j)) := by sorry

end KallenbergLP.AverageLP
