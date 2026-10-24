-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_legendre_ne_bot_iff_408915f
-- name    : FunctionalInequalities.Analysis.legendre_ne_bot_iff_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:20:23.816576+00:00
-- url     : https://prove2.me/theorems/2cab44e7-d3a6-4d27-85a8-01e07386d771
-- title:
--   Characterization of Finite-Above Legendre Values
-- statement:
--   This characterizes when a Legendre transform value is not negative infinity.
--
--   Let $\phi:E\to\overline{\mathbb R}$ and $y\in E$. Then
--
--   $$
--   \operatorname{Leg}(\phi)(y)\neq-\infty
--   \quad\Longleftrightarrow\quad
--   \exists x\in E,\ \phi(x)\neq+\infty.
--   $$
--
--   Thus the conjugate avoids $-\infty$ exactly when the effective domain of $\phi$ is nonempty. No convexity, measurability, or finiteness assumptions are imposed on the input.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Convex/Legendre.lean#L180-L204 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Convex.Legendre`, declaration `FunctionalInequalities.Analysis.legendre_ne_bot_iff`; the repository is private at upload time).

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

theorem FunctionalInequalities.Analysis.legendre_ne_bot_iff_408915f (φ : E → EReal) (y : E) :
    legendre φ y ≠ ⊥ ↔ ∃ x, φ x ≠ ⊤ := by sorry
