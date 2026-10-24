-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_exists_coercive_tilt_of_mem_interior_legendre_domain_408915f
-- name    : FunctionalInequalities.Analysis.exists_coercive_tilt_of_mem_interior_legendre_domain_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:16:36.569472+00:00
-- url     : https://prove2.me/theorems/e66dd3e6-02ac-4533-9eeb-273754ee42e9
-- title:
--   Linear Coercivity of an Interior Legendre Tilt
-- statement:
--   This is a pointwise coercivity result for a proper extended-real potential.
--
--   Let $E$ be a finite-dimensional real inner-product normed space, let $\phi:E\to\overline{\mathbb R}$ be a `ProperPotential`, and let $y$ lie in the interior of the finite domain
--   $$\{q:E\mid \operatorname{legendre}(\phi)(q)\ne+\infty\}.$$
--
--   Then there exist real numbers $a,b$ with $a>0$ such that, for every $z\in E$,
--   $$\bigl(a\|z\|-b\bigr)\le \phi(z)-\langle z,y\rangle,$$
--   where the real affine expression is embedded into `EReal` and the inner product is likewise coerced.
--
--   No convexity, differentiability, nonnegativity, or global finiteness of $\phi$ is assumed. The result supplies the linear decay needed to establish attainment of a Legendre supremum.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Convex/LegendreVariation/Attainment.lean#L207-L275 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Convex.LegendreVariation.Attainment`, declaration `FunctionalInequalities.Analysis.exists_coercive_tilt_of_mem_interior_legendre_domain`; the repository is private at upload time).

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_AffineMaximum
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_Legendre
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Analysis.Normed.Affine.Convex
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Data.EReal.Operations
import Mathlib.Topology.Instances.EReal.Lemmas
import Mathlib.Topology.Semicontinuity.Basic

noncomputable section
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis
section Attainment
open Set
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem FunctionalInequalities.Analysis.exists_coercive_tilt_of_mem_interior_legendre_domain_408915f
    (φ : E → EReal) (hφ : ProperPotential φ) (y : E)
    (hy : y ∈ interior {q : E | legendre φ q ≠ ⊤}) :
    ∃ (a b : ℝ), 0 < a ∧ ∀ z : E,
      ((a * ‖z‖ - b : ℝ) : EReal) ≤ φ z - (inner ℝ z y : EReal) := by sorry
