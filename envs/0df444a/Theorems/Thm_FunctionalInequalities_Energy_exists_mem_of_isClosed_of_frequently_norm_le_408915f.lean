-- Prove2me | Theorems.Thm_FunctionalInequalities_Energy_exists_mem_of_isClosed_of_frequently_norm_le_408915f
-- name    : FunctionalInequalities.Energy.exists_mem_of_isClosed_of_frequently_norm_le_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:28:50.273993+00:00
-- url     : https://prove2.me/theorems/b07fa45b-da64-4495-b3f1-29d37c56a7b0
-- title:
--   Closed-Subspace Selection With A Frequently Bounded Hilbert Component
-- statement:
--   This is a closed-subspace selection lemma in a product of normed spaces.
--
--   Let $X$ be a real normed space, let $H$ be a complete real Hilbert space, and let $G\subseteq X\times H$ be a closed real submodule. Suppose sequences $x_n\in X$ and $y_n\in H$ satisfy
--
--   1. $(x_n,y_n)\in G$ for every $n$;
--   2. $x_n\to x_0$;
--   3. for some real $L$, the inequality $\|y_n\|\le L$ holds frequently along $n\to\infty$.
--
--   Then there exists $y_0\in H$ such that
--
--   $$
--   (x_0,y_0)\in G,
--   \qquad
--   \|y_0\|\le L.
--   $$
--
--   The Lean declaration is `exists_mem_of_isClosed_of_frequently_norm_le`. “Frequently” is the filter-theoretic condition along `atTop`, not an eventual bound.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Energy/Relaxation/LinearPMap.lean#L47-L162 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Energy.Relaxation.LinearPMap`, declaration `FunctionalInequalities.Energy.exists_mem_of_isClosed_of_frequently_norm_le`; the repository is private at upload time).

import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Form_Functional
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Form_QuadraticPreEnergy
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Relaxation_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Relaxation_LinearPMap
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.ENNReal.Inv
import Mathlib.Topology.Algebra.Module.LinearPMap
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Topology.Order.LiminfLimsup

noncomputable section
open Filter Topology Set
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Energy
end FunctionalInequalities.Energy
open FunctionalInequalities FunctionalInequalities.Energy
section Selection
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

theorem FunctionalInequalities.Energy.exists_mem_of_isClosed_of_frequently_norm_le_408915f
    {G : Submodule ℝ (X × H)} (hG : IsClosed (G : Set (X × H)))
    {x : ℕ → X} {y : ℕ → H} (hxy : ∀ n, (x n, y n) ∈ G)
    {x₀ : X} (hx : Tendsto x atTop (𝓝 x₀)) {L : ℝ} (hL : ∃ᶠ n in atTop, ‖y n‖ ≤ L) :
    ∃ y₀ : H, (x₀, y₀) ∈ G ∧ ‖y₀‖ ≤ L := by sorry
