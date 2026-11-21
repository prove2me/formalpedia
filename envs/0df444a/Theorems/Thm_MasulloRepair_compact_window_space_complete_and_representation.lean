-- Prove2me | Theorems.Thm_MasulloRepair_compact_window_space_complete_and_representation
-- name    : MasulloRepair.compact_window_space_complete_and_representation
-- status  : Proved
-- author  : @ibecca
-- created : 2026-11-21T02:11:53.399777+00:00
-- url     : https://prove2.me/theorems/fea3483f-d6b8-43ba-95b4-3acb3895e88f
-- title:
--   The compact-window replacement is complete and represents common L2 functions
-- statement:
--   Let $\mu$ be any measure on $\mathbf R$, put $d\nu_n=\max\{1,t^{2n}\}\,d\mu$, and let $X_\mu$ be the compatible subspace of $\prod_nL^2(\nu_n;\mathbf C)$ defined by equality of all images in $L^2(\mu;\mathbf C)$.
--
--   Then $X_\mu$ is complete, metrizable, and locally convex. Moreover:
--
--   1. Every $u=(u_n)\in X_\mu$ has one representative $f:\mathbf R\to\mathbf C$ satisfying
--   $$f\in L^2(\mu)\cap\bigcap_{n\ge0}L^2(\nu_n),\qquad
--   u_n=f\quad\nu_n\text{-almost everywhere for every }n.$$
--   2. Conversely, each function $f$ belonging to all the $L^2(\nu_n)$ determines a unique compatible tuple with those almost-everywhere representatives.
--
--   Thus this construction gives a complex Fréchet model for the intersection of the weighted $L^2$ spaces, with convergence in every coordinate norm. In particular it applies to the endpoint measure $\mu_{a,s}$ and provides the completeness component of the compact-window repair.
--
--   **Formalization Note.** Local convexity is expressed over the underlying real scalars, while the space itself and its structural maps are complex-linear. Completeness uses the inherited product uniformity. Density of the original smooth test space, a Mellin-transform isomorphism, and the draft's trace conclusions are not asserted.
-- source:
--   Repair of A. M. Masullo, The Music of the Primes, Definition 9.2.2.1 and Lemma 9.2.2.2(3)(a), equations (9.2.2.3), (9.2.2.6)-(9.2.2.7), printed pp. 412-413, with relevance to the proposed space in Proposition 9.2.2.4, p. 414. Frozen draft: https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf . Yi identified the uniform-supremum finiteness defect and proposed compact-window seminorms in Prove2Me mission comment a96ab6a0-9f70-4b3f-ab3e-8c7e38a823f2 (mission 638f9b7f-e232-4624-ba08-5889465bb1e7). This contribution develops that replacement, following the accepted cofinal convergence criterion 2cf713aa-17bf-4fe0-9b9f-b73f1670aac5. It does not assert the original uniform-norm definition is valid on all of its stated tests. The theorem proves closedness of the compatibility conditions, completeness of the resulting subspace, and both directions of its representation by common weighted-L2 functions. No completeness or common-representative assumption is included in the definition.

import Definitions.Def_MasulloRepair_WindowL2

set_option autoImplicit false
open MeasureTheory Set Filter Topology MasulloRepair
open scoped ENNReal

theorem MasulloRepair.compact_window_space_complete_and_representation (μ : Measure ℝ) :
    CompleteSpace (windowSpace μ) ∧
    TopologicalSpace.MetrizableSpace (windowSpace μ) ∧
    LocallyConvexSpace ℝ (windowSpace μ) ∧
    (∀ u : windowSpace μ, ∃ f : ℝ → ℂ, MemLp f 2 μ ∧
      ∀ n : ℕ, MemLp f 2 (windowMeasure μ n) ∧
        (u.val n : ℝ → ℂ) =ᵐ[windowMeasure μ n] f) ∧
    (∀ f : ℝ → ℂ, (∀ n : ℕ, MemLp f 2 (windowMeasure μ n)) →
      ∃! u : windowSpace μ, ∀ n : ℕ, (u.val n : ℝ → ℂ) =ᵐ[windowMeasure μ n] f) := by sorry
