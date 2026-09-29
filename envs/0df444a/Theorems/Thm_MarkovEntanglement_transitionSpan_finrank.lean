-- Prove2me | Theorems.Thm_MarkovEntanglement_transitionSpan_finrank
-- name    : MarkovEntanglement.transitionSpan_finrank
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-08-07T13:53:39.255175+00:00
-- url     : https://prove2.me/theorems/f7a8b001-d909-4743-adaf-6b2e2453243f
-- title:
--   Dimension of the span of transition matrices
-- statement:
--   ## Statement
--
--   **Lemma.** Let $\Omega_P \subseteq \mathbb{R}^{m \times m}$ be the linear span of the
--   $m \times m$ transition matrices. Then
--   $$\dim(\Omega_P) \;=\; m^2 - m + 1 .$$
--
--   ## Notes
--
--   The transition matrices form an affine set, not a subspace — each row must sum to one — so
--   their span is a proper subspace of all $m \times m$ matrices, of codimension $m - 1$. A basis
--   is given by the matrices $Z_{ij}$ that put a one at $(i,j)$ and along the diagonal.
--
--   The count matters for the entanglement theory: the minimal subspace containing all
--   *separable* transitions on a product space has dimension $\dim(\Omega_P)^2$, which is how one
--   sees that separable matrices are a thin subset of all joint transitions — most multi-agent
--   systems are entangled.
--
--   Search terms: dimension of the space of stochastic matrices, affine span row-stochastic,
--   codimension of transition matrices.
-- source:
--   Shuze Chen and Tianyi Peng, *Multi-agent Markov Entanglement*, arXiv:2506.02385v3, Lemma 3, p. 34

import Mathlib
import Definitions.Def_markov_entanglement_multi

open scoped BigOperators
open MarkovEntanglement

namespace MarkovEntanglement

theorem transitionSpan_finrank (m : ℕ) (hm : 0 < m) :
    Module.finrank ℝ (transitionSpan (Fin m)) = m ^ 2 - m + 1 := by
  sorry

end MarkovEntanglement
