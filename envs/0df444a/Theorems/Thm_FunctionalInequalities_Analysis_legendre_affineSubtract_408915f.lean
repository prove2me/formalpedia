-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_legendre_affineSubtract_408915f
-- name    : FunctionalInequalities.Analysis.legendre_affineSubtract_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:20:26.909779+00:00
-- url     : https://prove2.me/theorems/481a8de1-5061-44cf-9f66-d02b858da4ad
-- title:
--   Legendre Transform Under Affine Subtraction
-- statement:
--   This gives the exact conjugation formula for subtracting an affine function.
--
--   Let $f:E\to\overline{\mathbb R}$, $a,y\in E$, and $b\in\mathbb R$. For the definition `affineSubtract f a b`, namely
--
--   $$
--   (\operatorname{affineSubtract} f\ a\ b)(x)=f(x)-\bigl(\langle a,x\rangle+b\bigr),
--   $$
--
--   one has
--
--   $$
--   \operatorname{Leg}(\operatorname{affineSubtract}(f,a,b))(y)
--   =
--   \operatorname{Leg}(f)(y+a)+b.
--   $$
--
--   The equality is in `EReal` and remains valid with infinite input or conjugate values.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Convex/Affine.lean#L39-L59 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Convex.Affine`, declaration `FunctionalInequalities.Analysis.legendre_affineSubtract`; the repository is private at upload time).

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_Affine
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_Legendre
import Mathlib.Analysis.Convex.Continuous
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.LocallyConvex.Separation
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
section
open scoped ENNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem FunctionalInequalities.Analysis.legendre_affineSubtract_408915f (f : E → EReal) (a : E) (b : ℝ) (y : E) :
    legendre (affineSubtract f a b) y = legendre f (y + a) + (b : EReal) := by sorry
