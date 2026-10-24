-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_legendre_norm_408915f
-- name    : FunctionalInequalities.Analysis.legendre_norm_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:20:24.828914+00:00
-- url     : https://prove2.me/theorems/6e9e8a2c-8f66-4a96-a09a-55f2142094cd
-- title:
--   Legendre Transform of the Norm
-- statement:
--   This computes the extended-real Legendre transform of the norm.
--
--   For every $y$ in a real inner-product space,
--
--   $$
--   \operatorname{Leg}\bigl(x\mapsto\|x\|\bigr)(y)
--   =
--   \begin{cases}
--   0,&\|y\|\leq1,\\
--   +\infty,&\|y\|>1.
--   \end{cases}
--   $$
--
--   The equality is in `EReal`. Thus the conjugate of the norm is the indicator of the closed unit ball, with value $0$ on the ball and $+\infty$ outside.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Convex/Legendre.lean#L310-L342 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Convex.Legendre`, declaration `FunctionalInequalities.Analysis.legendre_norm`; the repository is private at upload time).

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
section
open Set Filter
open scoped ENNReal Topology
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem FunctionalInequalities.Analysis.legendre_norm_408915f (y : E) :
    legendre (fun x : E => (‖x‖ : EReal)) y = if ‖y‖ ≤ 1 then 0 else ⊤ := by sorry
