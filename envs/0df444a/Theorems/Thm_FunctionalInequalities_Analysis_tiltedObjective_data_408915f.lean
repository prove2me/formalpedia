-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_tiltedObjective_data_408915f
-- name    : FunctionalInequalities.Analysis.tiltedObjective_data_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:17:57.624034+00:00
-- url     : https://prove2.me/theorems/3ba7c31e-fbb5-4ccb-8504-0266fbe471c3
-- title:
--   Regularity and Coercive Decay of the Tilted Objective
-- statement:
--   This is a technical attainment lemma for a Legendre transform.
--
--   Let $E$ be a finite-dimensional real inner-product normed space, let $\phi:E\to\overline{\mathbb R}$ be a `ProperPotential`, and assume that $\phi$ is lower semicontinuous. If $y$ lies in the interior of $\{q:\phi^*(q)\ne+\infty\}$, define $G(z)=\langle z,y\rangle-\phi(z)$. Then:
--
--   1. $G$ is upper semicontinuous;
--   2. $G(z)\ne+\infty$ for every $z$;
--   3. $G(z)\ne-\infty$ for at least one $z$; and
--   4. there exist $a,b\in\mathbb R$ with $a>0$ such that, for every $z$,
--   $$G(z)\le b-a\|z\|.$$
--
--   The conclusion supplies the hypotheses for a separate upper-semicontinuous maximum theorem; it does not itself assert existence of a maximizer.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Convex/LegendreVariation/Attainment.lean#L277-L332 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Convex.LegendreVariation.Attainment`, declaration `FunctionalInequalities.Analysis.tiltedObjective_data`; the repository is private at upload time).

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

theorem FunctionalInequalities.Analysis.tiltedObjective_data_408915f
    (φ : E → EReal) (hφ : ProperPotential φ)
    (hlsc : LowerSemicontinuous φ) (y : E)
    (hy : y ∈ interior {q : E | legendre φ q ≠ ⊤}) :
    let G : E → EReal := fun z => (inner ℝ z y : EReal) - φ z
    UpperSemicontinuous G ∧
      (∀ z, G z ≠ ⊤) ∧
      (∃ z, G z ≠ ⊥) ∧
      ∃ (a b : ℝ), 0 < a ∧ ∀ z,
        G z ≤ ((b - a * ‖z‖ : ℝ) : EReal) := by sorry
