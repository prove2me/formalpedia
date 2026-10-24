-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_exists_pos_alexandrov_maximum_principle_408915f
-- name    : FunctionalInequalities.Analysis.exists_pos_alexandrov_maximum_principle_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:13:49.169979+00:00
-- url     : https://prove2.me/theorems/6917a1f2-e55c-4175-9124-5452e8fa904d
-- title:
--   Alexandrov Maximum Principle
-- statement:
--   This formalizes the Alexandrov maximum principle, cited as Theorem 1.4.2 in Gutiérrez's treatment of the Monge–Ampère equation.
--
--   Let $E$ be a nontrivial finite-dimensional real inner-product space with measurable and Borel structures, and write $n=\dim E$. There exists $c>0$, depending only on $E$, such that for every convex $u:E\to\mathbb R$, every bounded open convex $\Omega$, and every $x_0\in\Omega$ with $u(x_0)<0$ and $u\ge0$ on $\partial\Omega$,
--
--   $$
--   \operatorname{ofReal}\!\left(c(-u(x_0))^n\right)
--   \le
--   \operatorname{vol}(\operatorname{subgradientImage}(u,\Omega))\,\operatorname{ofReal}\!\left(\operatorname{diam}(\Omega)^{n-1}\operatorname{infDist}(x_0,\partial\Omega)\right).
--   $$
--
--   The volume is an `ENNReal` value and the real factors are embedded with `ofReal`. The declaration is `exists_pos_alexandrov_maximum_principle`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Convex/Alexandrov.lean#L1216-L1397 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Convex.Alexandrov`, declaration `FunctionalInequalities.Analysis.exists_pos_alexandrov_maximum_principle`; the repository is private at upload time).

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_AffineMaximum
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_Alexandrov
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_Legendre
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_Subgradient
import Mathlib
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.Convex.Continuous
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Measure
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Normed.Affine.Convex
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Data.EReal.Operations
import Mathlib.Topology.Instances.EReal.Lemmas
import Mathlib.Topology.Semicontinuity.Basic

noncomputable section
open MeasureTheory Set
open scoped RealInnerProductSpace ENNReal
section LT11C5AlexandrovMaximumPrinciple
open MeasureTheory Set Metric
open scoped RealInnerProductSpace ENNReal
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis
section InnerProduct
variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem FunctionalInequalities.Analysis.exists_pos_alexandrov_maximum_principle_408915f [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E]
    [BorelSpace E] :
    ∃ c : ℝ, 0 < c ∧ ∀ (u : E → ℝ), ConvexOn ℝ univ u → ∀ (Ω : Set E), IsOpen Ω → Convex ℝ Ω →
      Bornology.IsBounded Ω → (∀ x ∈ frontier Ω, 0 ≤ u x) → ∀ x₀ ∈ Ω, u x₀ < 0 →
      ENNReal.ofReal (c * (-u x₀) ^ Module.finrank ℝ E) ≤
        (volume : Measure E) (subgradientImage u Ω) *
          ENNReal.ofReal (diam Ω ^ (Module.finrank ℝ E - 1) * infDist x₀ (frontier Ω)) := by sorry
