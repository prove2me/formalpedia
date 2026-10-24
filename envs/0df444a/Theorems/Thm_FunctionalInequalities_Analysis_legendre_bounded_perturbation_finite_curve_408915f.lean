-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_legendre_bounded_perturbation_finite_curve_408915f
-- name    : FunctionalInequalities.Analysis.legendre_bounded_perturbation_finite_curve_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:20:23.933053+00:00
-- url     : https://prove2.me/theorems/4c068413-b8cf-4ef2-873d-be8c3878957a
-- title:
--   Finite Legendre Curve Under Bounded Perturbations
-- statement:
--   This gives a finite real-valued perturbation curve for the Legendre transform.
--
--   Let $\phi:E\to\overline{\mathbb R}$ be proper and let $y\in E$ satisfy $\operatorname{Leg}(\phi)(y)\neq+\infty$. Let $b:E\to\mathbb R$, let $M\geq0$, and assume $|b(z)|\leq M$ for every $z$. For every $t\in\mathbb R$, define
--
--   $$
--   \psi_t=\operatorname{Leg}(z\mapsto\phi(z)+t b(z))(y).
--   $$
--
--   Then $\psi_t$ is neither $+\infty$ nor $-\infty$, and
--
--   $$
--   \left|\operatorname{toReal}(\psi_t)-\operatorname{toReal}(\operatorname{Leg}(\phi)(y))\right|
--   \leq |t|M.
--   $$
--
--   This is the finite-value consequence of the extended-real perturbation estimate and is useful for treating Legendre variations as real curves.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Convex/LegendreVariation/Perturbation.lean#L125-L185 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Convex.LegendreVariation.Perturbation`, declaration `FunctionalInequalities.Analysis.legendre_bounded_perturbation_finite_curve`; the repository is private at upload time).

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_Legendre
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Analysis.Normed.Module.Convex
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
section FiniteCurve
set_option autoImplicit false
set_option relaxedAutoImplicit false
open Set

theorem FunctionalInequalities.Analysis.legendre_bounded_perturbation_finite_curve_408915f
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (φ : E → EReal) (hφ : ProperPotential φ) (y : E)
    (hy : legendre φ y ≠ ⊤)
    (b : E → ℝ) (M : ℝ) (hM : 0 ≤ M)
    (hb : ∀ z : E, |b z| ≤ M) :
    ∀ t : ℝ,
      let ψ := legendre (fun z : E => φ z + ((t * b z : ℝ) : EReal)) y
      ψ ≠ ⊤ ∧ ψ ≠ ⊥ ∧
        |ψ.toReal - (legendre φ y).toReal| ≤ |t| * M := by sorry
