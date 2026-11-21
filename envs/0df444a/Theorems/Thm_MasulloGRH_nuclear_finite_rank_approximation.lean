-- Prove2me | Theorems.Thm_MasulloGRH_nuclear_finite_rank_approximation
-- name    : MasulloGRH.nuclear_finite_rank_approximation
-- status  : Proved
-- author  : @ghseeli
-- created : 2026-11-21T00:35:21.572425+00:00
-- url     : https://prove2.me/theorems/4c0fe470-87d5-49b6-9dd1-b90d391782c2
-- title:
--   Finite-rank approximation on bounded sets for maps from nuclear spaces
-- statement:
--   Let $E$ be a nuclear Hausdorff locally convex complex vector space, $T:E\to F$ a continuous complex-linear map, $B\subseteq E$ a bounded set, $q$ a continuous seminorm on $F$, and $\varepsilon>0$. There are finitely many continuous linear functionals $\varphi_1,\ldots,\varphi_N\in E^\prime$ and vectors $y_1,\ldots,y_N\in F$ such that $$q\!\left(Tx-\sum_{j=1}^N\varphi_j(x)y_j\right)<\varepsilon\qquad(x\in B).$$ Thus continuous maps from nuclear spaces admit finite-rank approximations uniformly on a prescribed bounded set in each continuous target seminorm. Taking $T$ to be the identity gives the corresponding approximation property.
--
--   This is the neighborhood-estimate formulation of the finite-rank density assertion in Remark C.2.4.17. Finite families of target seminorms and bounded sets can be absorbed into a maximum seminorm and finite union, respectively. No completeness, metrizability, barrelledness, or quasi-completeness assumption on $E$ is required.
--
--   Formalization Note: the statement records the approximants explicitly as finite sums of continuous rank-one maps. It does not package them as a separate dense subset of an operator-topology type; the target is only required to carry the displayed vector-space structure, topology, continuous map, and continuous seminorm.
-- source:
--   A. M. Masullo, The Music of the Primes, frozen 20 November 2026 draft, p. 690, Lemma C.2.4.16(2) and especially Remark C.2.4.17: density of the image of E′ tensor F in L_beta(E,F), i.e. finite-rank approximation uniformly on bounded sets. https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf. Formalization is the explicit bounded-set/continuous-seminorm neighborhood estimate.

import Definitions.Def_MasulloGRH_LocallyConvex
set_option autoImplicit false
open MasulloGRH Filter Topology Set
open scoped BigOperators

theorem MasulloGRH.nuclear_finite_rank_approximation (E F : Type*) [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    [AddCommGroup F] [Module ℂ F] [TopologicalSpace F]
    (hE : IsNuclear E) (T : E →L[ℂ] F) (B : Set E)
    (hB : Bornology.IsVonNBounded ℂ B) (q : Seminorm ℂ F) (hq : Continuous q)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ (N : ℕ) (φ : Fin N → StrongDual ℂ E) (y : Fin N → F),
      ∀ x ∈ B, q (T x - ∑ i, φ i x • y i) < ε := by sorry
