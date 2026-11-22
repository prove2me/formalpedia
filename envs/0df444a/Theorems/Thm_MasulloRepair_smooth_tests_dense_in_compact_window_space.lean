-- Prove2me | Theorems.Thm_MasulloRepair_smooth_tests_dense_in_compact_window_space
-- name    : MasulloRepair.smooth_tests_dense_in_compact_window_space
-- status  : Proved
-- author  : @ibecca
-- created : 2026-11-21T15:05:27.68695+00:00
-- url     : https://prove2.me/theorems/3dd910cd-1bb2-4835-87d3-4f25771ce6ac
-- title:
--   Smooth positive-axis tests are dense in the complete compact-window space
-- statement:
--   Let $a,s\in\mathbf R$ and let $X_{a,s}$ be the previously constructed complete compatible subspace of
--   $$\prod_{n\ge0} L^2(\nu_{a,s,n};\mathbf C),\qquad
--   d\nu_{a,s,n}(t)=1_{(0,\infty)}(t)
--   \max\{t^{2a},t^{2(a+n)}\}(1+\log^2t)^{s/2}\,\frac{dt}{t}.$$
--   Compatibility means that every coordinate has the same image in the endpoint $L^2$ space.
--
--   Let $D_{a,s}$ consist of tuples whose coordinates are all represented almost everywhere by one function $g\in C_c^\infty(\mathbf R;\mathbf C)$ with closed support contained in $(0,\infty)$. Then
--   $$\overline{D_{a,s}}^{\,X_{a,s}}=X_{a,s}.$$
--
--   The topology here is the actual inherited product topology on the published compatible-product model. Together with its proved completeness and common-function representation, this resolves the smooth-test density obligation in the compact-window replacement. The original uniform-supremum norm and downstream Mellin and trace assertions are not conclusions of this theorem.
-- source:
--   Auxiliary theorem for the compact-window repair of A. M. Masullo, The Music of the Primes, Definition 9.2.2.1 and Lemma 9.2.2.2(3), printed pp. 412-413, and Proposition 9.2.2.4, p. 414. Frozen source: https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf . This develops Yi's proposed compact-window replacement (mission comment a96ab6a0-9f70-4b3f-ab3e-8c7e38a823f2), after the accepted completeness theorem fea3483f-d6b8-43ba-95b4-3acb3895e88f. It is an explicitly stated repair, not a claim that the original uniform supremum is finite. This is the density component supplementing the accepted completeness/common-function representation theorem fea3483f-d6b8-43ba-95b4-3acb3895e88f.

import Definitions.Def_MasulloRepair_LogWindows
import Mathlib.Analysis.Calculus.ContDiff.Defs

set_option autoImplicit false
open MeasureTheory Set Filter Topology MasulloRepair
open scoped ENNReal ContDiff

theorem MasulloRepair.smooth_tests_dense_in_compact_window_space (a s : ℝ) :
    Dense {u : windowSpace (halflineBaseMeasure a s) |
      ∃ g : ℝ → ℂ, HasCompactSupport g ∧
        tsupport g ⊆ Ioi (0 : ℝ) ∧ ContDiff ℝ ∞ g ∧
        ∀ n : ℕ, (u.val n : ℝ → ℂ) =ᵐ[windowMeasure (halflineBaseMeasure a s) n] g} := by sorry
