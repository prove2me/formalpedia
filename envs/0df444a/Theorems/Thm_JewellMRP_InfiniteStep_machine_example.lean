-- Prove2me | Theorems.Thm_JewellMRP_InfiniteStep_machine_example
-- name    : JewellMRP.InfiniteStep.machine_example
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T10:34:16.341571+00:00
-- url     : https://prove2.me/theorems/7492e6e3-ea71-4927-af0f-d7a1da198af0
-- title:
--   Example, pp. 961–962 — gains $70, 50, 80, 60$; $(B,A)$ optimal for all $n$ with $V_1(n) = 80n+170+(-1)^{n+1}170$; Cesàro biases $\pm 170$
-- statement:
--   The paper's two-state machine maintenance-repair example. State 1 is "running", state 2 "broken down". Every alternative moves the machine to the other state with probability one, so under every stationary policy the embedded chain is
--   $$P = \begin{pmatrix} 0 & 1 \\ 1 & 0 \end{pmatrix}.$$
--   With the linear reward structure (8) ($R'_{ij} = R_{ij}$, $R''_{ij} = 0$) the one-step expected reward of an alternative is $R_{ij} + r_{ij}\nu_{ij}$:
--   in state 1, alternative $A$ gives $0 + 100\cdot 4 = 400$ and alternative $B$ gives $0 + 84 \cdot 5 = 420$;
--   in state 2, alternative $A$ gives $0 + (-65)\cdot 4 = -260$ and alternative $B$ gives $-100 + (-200)\cdot 1 = -300$.
--   Let $\rho = (420, -260)$ be the reward vector of the policy $(B,A)$, $V(0) = 0$, and $\pi = (\tfrac12, \tfrac12)$. Then
--
--   1. $P$ is ergodic (irreducible, row-stochastic, of period $2$) and $\pi$ is a stationary probability vector;
--   2. the gains $G = \sum_i \pi_i \rho_i$ of the four stationary policies are $G^{AA} = 70$, $G^{AB} = 50$, $G^{BA} = 80$, $G^{BB} = 60$;
--   3. $(B,A)$ is optimal for every $n$: the return $V(n)$ of $(B,A)$ satisfies the optimality recursion (I 16),
--   $$V_i(n+1) = \max_{z \in \{A, B\}} \Bigl[\rho_i^z + \sum_j p_{ij} V_j(n)\Bigr], \qquad i = 1, 2,\ n \ge 0,$$
--   so it is the optimal $n$-step return;
--   4. for every $n \ge 0$,
--   $$V_1(n) = 80n + 170 + (-1)^{n+1}170, \qquad V_2(n) = 80n - 170 - (-1)^{n+1}170 ;$$
--   5. the limiting bias vector is $(Z - \Pi)\rho + \Pi V(0) = (170, -170)$;
--   6. the relative values $V_1 = 340$, $V_2 = 0$ solve equations (5): $V_i + G = \rho_i + \sum_j p_{ij} V_j$ with $G = 80$.
--
--   The example shows why the bias limit is a Cesàro limit: $W(n) = V(n) - 80n$ oscillates between two values forever, and only its average converges.
--
--   **Formalization Note** States 1 and 2 are the Lean indices `0` and `1`, and the paper's $(-)^{n+1}$ is $(-1)^{n+1}$. The paper's "optimal for all values of $n$" is stated as: the $(B,A)$ return satisfies (I 16) with the maximum over both alternatives in each state, which determines the optimal return uniquely from $V(0) = 0$. The rewards are written as $R + r\nu$ so that each number can be read off p. 961.
-- source:
--   Jewell, Markov-Renewal Programming. II: Infinite Return Models, Example, Oper. Res. 11 (1963), pp. 961-962, An Example, Fig. 4

import Mathlib
import Definitions.Def_JewellMRP_InfiniteStep_Model

open Matrix Filter Topology

namespace JewellMRP.InfiniteStep

theorem machine_example :
    let P : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; 1, 0]
    let ρA₁ : ℝ := 0 + 100 * 4
    let ρB₁ : ℝ := 0 + 84 * 5
    let ρA₂ : ℝ := 0 + (-65) * 4
    let ρB₂ : ℝ := -100 + (-200) * 1
    let ρ : Fin 2 → ℝ := ![ρB₁, ρA₂]
    let π : Fin 2 → ℝ := ![1 / 2, 1 / 2]
    IsErgodic P ∧ IsStationary P π ∧
      gain π ![ρA₁, ρA₂] = 70 ∧ gain π ![ρA₁, ρB₂] = 50 ∧ gain π ρ = 80 ∧
      gain π ![ρB₁, ρB₂] = 60 ∧
      (∀ n : ℕ,
        stepReturn P ρ 0 (n + 1) 0 =
            max (ρA₁ + ∑ j, P 0 j * stepReturn P ρ 0 n j)
              (ρB₁ + ∑ j, P 0 j * stepReturn P ρ 0 n j) ∧
          stepReturn P ρ 0 (n + 1) 1 =
            max (ρA₂ + ∑ j, P 1 j * stepReturn P ρ 0 n j)
              (ρB₂ + ∑ j, P 1 j * stepReturn P ρ 0 n j)) ∧
      (∀ n : ℕ, stepReturn P ρ 0 n 0 = 80 * n + 170 + (-1) ^ (n + 1) * 170 ∧
        stepReturn P ρ 0 n 1 = 80 * n - 170 - (-1) ^ (n + 1) * 170) ∧
      (fundamentalMatrix P π - limitMatrix π) *ᵥ ρ + limitMatrix π *ᵥ 0 = ![170, -170] ∧
      (∀ i, ![340, 0] i + gain π ρ = ρ i + ∑ j, P i j * ![(340 : ℝ), 0] j) := by sorry

end JewellMRP.InfiniteStep
