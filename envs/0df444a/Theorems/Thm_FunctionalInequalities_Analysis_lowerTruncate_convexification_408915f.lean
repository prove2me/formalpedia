-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_lowerTruncate_convexification_408915f
-- name    : FunctionalInequalities.Analysis.lowerTruncate_convexification_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:20:32.267709+00:00
-- url     : https://prove2.me/theorems/5a03e8cd-4e55-4b15-8111-1802cbaa0fbf
-- title:
--   Convexification of a Lower Truncation
-- statement:
--   This formalizes the convexification statement corresponding to Proposition 12 of Cordero–Erausquin–Klartag (arXiv:1304.0630v1).
--
--   Let $\phi:E\to\overline{\mathbb R}$ and $M\in\mathbb R$. Assume that $\phi$ has at least one point where it is not $+\infty$. Define
--
--   $$
--   g=\max(\phi,-M),\qquad c=\operatorname{Leg}(\operatorname{Leg}(g)).
--   $$
--
--   Then $c$ is a convex proper lower-semicontinuous potential, and for every $x$,
--
--   $$
--   -M\leq c(x)\leq g(x).
--   $$
--
--   Moreover, the conjugate is preserved:
--
--   $$
--   \operatorname{Leg}(c)(y)=\operatorname{Leg}(g)(y)
--   $$
--
--   for every $y$. The construction requires no convexity assumption on the original $\phi$.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Convex/Legendre.lean#L225-L245 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Convex.Legendre`, declaration `FunctionalInequalities.Analysis.lowerTruncate_convexification`; the repository is private at upload time).

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
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem FunctionalInequalities.Analysis.lowerTruncate_convexification_408915f (φ : E → EReal) (M : ℝ)
    (hfinite : ∃ x, φ x ≠ ⊤) :
    let g := lowerTruncate φ M
    let c := legendre (legendre g)
    ConvexPotential c ∧ LowerSemicontinuous c ∧ ProperPotential c ∧
      (∀ x, ((-M : ℝ) : EReal) ≤ c x ∧ c x ≤ g x) ∧
      (∀ y, legendre c y = legendre g y) := by sorry
