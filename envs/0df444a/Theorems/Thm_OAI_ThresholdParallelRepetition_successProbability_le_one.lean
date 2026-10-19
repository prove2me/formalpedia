-- Prove2me | Theorems.Thm_OAI_ThresholdParallelRepetition_successProbability_le_one
-- name    : OAI.ThresholdParallelRepetition.successProbability_le_one
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T10:39:50.815408+00:00
-- url     : https://prove2.me/theorems/9ac465c9-061e-409f-be9f-44d0fed9a34b
-- title:
--   The winning probability of an entangled strategy is at most one
-- statement:
--   Let $\mathcal X,\mathcal Y$ (questions) and $\mathcal A,\mathcal B$ (answers) be finite nonempty sets. A nonlocal game $G$ consists of a probability distribution $\pi$ on $\mathcal X\times\mathcal Y$ (so $\pi(x,y)\ge0$ and $\sum_{x,y}\pi(x,y)=1$) and an acceptance predicate $V(x,y,a,b)\in\{\mathrm{true},\mathrm{false}\}$.
--
--   An entangled strategy $S$ consists of dimensions $d_A,d_B\ge1$, a unit vector $\psi\in\mathbb C^{d_A}\otimes\mathbb C^{d_B}$ with coordinates $\psi(i,i')$ and $\sum_{i,i'}|\psi(i,i')|^2=1$, for each question $x\in\mathcal X$ a positive operator-valued measure $\{P^x_a\}_{a\in\mathcal A}$ of positive semidefinite $d_A\times d_A$ matrices with $\sum_aP^x_a=I$, and likewise for each $y\in\mathcal Y$ a family $\{Q^y_b\}_{b\in\mathcal B}$ of positive semidefinite $d_B\times d_B$ matrices with $\sum_bQ^y_b=I$. Its Born probabilities are
--   $$
--   p_S(a,b\mid x,y)=\operatorname{Re}\big\langle\psi,(P^x_a\otimes Q^y_b)\,\psi\big\rangle=\operatorname{Re}\sum_{(i,i'),(j,j')}\overline{\psi(i,i')}\,(P^x_a)_{ij}\,(Q^y_b)_{i'j'}\,\psi(j,j'),
--   $$
--   and the success probability of $S$ in $G$ is
--   $$
--   \omega(G,S)=\sum_{(x,y)\in\mathcal X\times\mathcal Y}\pi(x,y)\sum_{(a,b)\in\mathcal A\times\mathcal B}\mathbf 1\big[V(x,y,a,b)\big]\,p_S(a,b\mid x,y).
--   $$
--
--   **Theorem.** For every game $G$ and every entangled strategy $S$,
--   $$
--   \omega(G,S)\le1 .
--   $$
--
--   The entangled value of $G$ is the supremum of $\omega(G,S)$ over all finite-dimensional entangled strategies. The bound shows that the set of success probabilities is bounded above, so this supremum is a genuine least upper bound and the entangled value is at most $1$; it is used whenever the entangled value is compared with the success probabilities of individual strategies.
--
--   **Formalization Note** The question and answer sets are `Fin (x+1)`, `Fin (y+1)`, `Fin (a+1)`, `Fin (b+1)`, and a single-round strategy (`SingleStrategy x y a b`) stores its local dimensions as `dimA + 1` and `dimB + 1`. The Born probability `Strategy.born` is the sum of the real parts of the displayed terms. The entangled value is defined with `sSup`, which returns a junk value on sets that are not bounded above; this lemma supplies the upper bound.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/EntangledGames/Basic.lean#L96-L111

import Mathlib
import Definitions.Def_EntangledGames
import Definitions.Def_OAI_Probability_EntangledGames_Basic

open OAI OAI.ThresholdParallelRepetition
open scoped BigOperators ComplexOrder
open scoped Kronecker
open Matrix

theorem OAI.ThresholdParallelRepetition.successProbability_le_one {x y a b : ℕ} (G : Game x y a b)
    (S : SingleStrategy x y a b) : successProbability G S ≤ 1 := by sorry
