-- Prove2me | Theorems.Thm_GraphLQGame_Equilibrium_transitive_regular
-- name    : GraphLQGame.Equilibrium.transitive_regular
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T12:25:27.891243+00:00
-- url     : https://prove2.me/theorems/46c9e508-8825-4718-a272-b4c764130cc5
-- title:
--   §2.2, p. 6 — a transitive graph is regular and $L_G = \delta(G)^{-1}A_G - I$ is symmetric
-- statement:
--   Let $G$ be a finite transitive graph without isolated vertices. Then $G$ is regular: all degrees equal a common value $\delta(G)$. Consequently
--   $$L_G=\frac{1}{\delta(G)}A_G-I,$$
--   and $L_G$ is a symmetric matrix.
--
--   Symmetry of $L_G$ is used throughout the proof of Theorem 2.5 (spectral decomposition, the Riccati boundary condition).
--
--   **Formalization Note** Vertices are `Fin n`; $L_G$ is the random-walk Laplacian.
-- source:
--   Lacker, Soret, A case study on stochastic games on large graphs in mean field and sparse regimes, arXiv:2005.14102v2 (2021), §2.2, p. 6, paragraph after the definition of L_G

import Mathlib
import Definitions.Def_GraphLQGame_Equilibrium_Graph

namespace GraphLQGame.Equilibrium

/-- Lacker–Soret, arXiv:2005.14102v2, §2.2, p. 6: a transitive graph is regular, and its
Laplacian is `L_G = δ(G)⁻¹ A_G − I`, a symmetric matrix.

Formalization Note: vertices are `Fin n` (the paper's `{1, …, n}` shifted to `{0, …, n−1}`);
`L_G` is the random-walk Laplacian `lap G = D⁻¹A − I`. -/
theorem transitive_regular {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hT : IsTransitive G) (hN : NoIsolated G) :
    (∀ u v : Fin n, G.degree u = G.degree v) ∧
      (∀ v : Fin n, lap G = ((G.degree v : ℝ))⁻¹ • G.adjMatrix ℝ - 1) ∧
      (lap G).transpose = lap G := by sorry

end GraphLQGame.Equilibrium
