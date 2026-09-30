-- Prove2me | Theorems.Thm_KellyStochasticNetworks_kirchhoff_from_random_walk
-- name    : KellyStochasticNetworks.kirchhoff_from_random_walk
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-18T15:57:35.463085+00:00
-- url     : https://prove2.me/theorems/086de9e8-6719-4253-b4cd-6e8f6ae3de5a
-- title:
--   Kirchhoff's node law from the random-walk game
-- statement:
--   Section 4.1 opens with a game. You perform a symmetric random walk on a graph with transition
--   rates $\gamma_{jk} = \gamma_{kj}$ until you hit a set $S$ of vertices, and you are then paid a
--   reward depending on the vertex you hit. Let $p_j$ be the expected reward starting from $j$.
--   Conditioning on the first vertex the walk jumps to gives, for every $j \notin S$,
--   $$p_j = \sum_i \frac{\gamma_{ji}}{\sum_k \gamma_{jk}}\,p_i .$$
--
--   This is exactly **Kirchhoff's node law**. For every $j \notin S$,
--   $$\sum_i \gamma_{ij}\,(p_i - p_j) = 0 .$$
--   Reading $p_i$ as the voltage at node $i$ and $\gamma_{ij}$ as the conductance — the inverse
--   resistance — of the edge $ij$, each term $\gamma_{ij}(p_i - p_j)$ is the current flowing into
--   node $j$ along that edge, and the identity says the currents into any interior node sum to
--   zero.
--
--   The equivalence is the first instance of the chapter's theme: a purely local rule, here the
--   random walk, produces a global pattern that is the solution of a network-wide problem. The
--   symmetry $\gamma_{ij} = \gamma_{ji}$, which is what makes the walk reversible, is exactly what
--   turns the averaging identity into a conservation law.
--
--   **Formalization Note** The vertex set is a finite index type and $S$ is a finite subset of it;
--   edges that are absent are represented by a zero rate, as in the book. The hypothesis that the
--   total rate out of an interior vertex is positive is what makes the averaging identity
--   meaningful. The probabilistic derivation of the averaging identity is not part of the
--   statement, which is the implication from it to the node law.
-- source:
--   Kelly & Yudovina, Stochastic Networks, CUP 2014, p. 87 (PDF p. 95), section 4.1.1: 'By conditioning on the first vertex i to which the random walk jumps from j, we obtain the relations p_j = sum_i (gamma_{ji} / sum_k gamma_{jk}) p_i, for j in G \ S. We can rewrite this set of equations as follows: 0 = sum_i gamma_{ij} (p_i - p_j), j in G \ S, p_j = v_j, j in S. Interpreting p_i as the voltage at vertex (node) i, and gamma_{ij} as the conductance (inverse resistance) of the edge (ij), the first line is asserting that the sum of the currents through all the edges into a given node i is 0. These are Kirchhoff's equations for an electrical network G.' sha256 ec271d555059aee58613e5e9a98b8346214b16185c527314f5d94c1ac8b17b6a

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Wardrop

namespace KellyStochasticNetworks

theorem kirchhoff_from_random_walk {n : ℕ} (γ : Fin n → Fin n → ℝ) (p : Fin n → ℝ)
    (S : Finset (Fin n)) (hsym : ∀ i j, γ i j = γ j i)
    (hdeg : ∀ j, j ∉ S → 0 < ∑ k, γ j k)
    (hp : ∀ j, j ∉ S → p j = ∑ i, (γ j i / ∑ k, γ j k) * p i) :
    ∀ j, j ∉ S → (∑ i, γ i j * (p i - p j)) = 0 := by sorry

end KellyStochasticNetworks
