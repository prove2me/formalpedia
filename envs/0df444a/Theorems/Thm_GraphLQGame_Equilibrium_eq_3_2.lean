-- Prove2me | Theorems.Thm_GraphLQGame_Equilibrium_eq_3_2
-- name    : GraphLQGame.Equilibrium.eq_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T12:26:39.033494+00:00
-- url     : https://prove2.me/theorems/15e50a16-d69d-494b-ab0b-66a4ac3af949
-- title:
--   (3.2), p. 19 — $\int x\,\mu_G(dx) = \frac1n\sum_i\lambda_i^G = \frac1n\mathrm{Tr}(L_G) = -1$, so $\mu_G \in \mathcal P_{\mathrm{Lap}}$
-- statement:
--   Let $G$ be a finite graph on $n\ge1$ vertices without isolated vertices, with Laplacian eigenvalues $\lambda^G_1,\dots,\lambda^G_n$. Since the adjacency matrix has zero trace,
--   $$\int_{[-2,0]}x\,\mu_G(dx)=\frac1n\sum_{i=1}^n\lambda_i^G=\frac1n\mathrm{Tr}(L_G)=-1,$$
--   and therefore (with Remark 2.4) $\mu_G$ is a probability measure on $[-2,0]$ with mean $-1$, i.e. $\mu_G\in\mathcal P_{\mathrm{Lap}}$.
--
--   This is what allows the results of §3, stated for $\mu\in\mathcal P_{\mathrm{Lap}}$, to be applied to $Q_G$.
--
--   **Formalization Note** The eigenvalues are the roots of the characteristic polynomial with multiplicity. The hypothesis $n\ge1$ is added: $\mu_G$ is a probability measure only for a nonempty graph.
-- source:
--   Lacker, Soret, A case study on stochastic games on large graphs in mean field and sparse regimes, arXiv:2005.14102v2 (2021), §3, p. 19, (3.2) and the sentences around it

import Mathlib
import Definitions.Def_GraphLQGame_Equilibrium_Graph
import Definitions.Def_GraphLQGame_Equilibrium_Spectral

open MeasureTheory

namespace GraphLQGame.Equilibrium

/-- Lacker–Soret, arXiv:2005.14102v2, §3, p. 19, display (3.2) and the sentence around it: for a
finite graph `G` on `n ≥ 1` vertices without isolated vertices, with Laplacian eigenvalues
`λ_1^G, …, λ_n^G`,
`∫_{[−2,0]} x µ_G(dx) = (1/n) Σ λ_i^G = (1/n) Tr(L_G) = −1`,
and `µ_G` belongs to `𝒫_Lap` (it is a probability measure on `[−2, 0]` with mean `−1`).

Formalization Note: the eigenvalues are the roots of the characteristic polynomial of `L_G`
with multiplicity; `0 < n` is added because `µ_G` is a probability measure only for a nonempty
graph. -/
theorem eq_3_2 {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hn : 0 < n)
    (hN : NoIsolated G) :
    ∫ x in Set.Icc (-2 : ℝ) 0, x ∂(specMeasure G) = (n : ℝ)⁻¹ * (lap G).charpoly.roots.sum ∧
      (n : ℝ)⁻¹ * (lap G).charpoly.roots.sum = (n : ℝ)⁻¹ * (lap G).trace ∧
      (n : ℝ)⁻¹ * (lap G).trace = -1 ∧
      IsPLap (specMeasure G) := by sorry

end GraphLQGame.Equilibrium
