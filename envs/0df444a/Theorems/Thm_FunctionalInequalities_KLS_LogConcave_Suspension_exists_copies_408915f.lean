-- Prove2me | Theorems.Thm_FunctionalInequalities_KLS_LogConcave_Suspension_exists_copies_408915f
-- name    : FunctionalInequalities.KLS.LogConcave.Suspension.exists_copies_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T14:35:32.754461+00:00
-- url     : https://prove2.me/theorems/b2245e27-4296-4ea1-ac20-af3fcf4247d8
-- title:
--   Existence Of A Suitable Number Of Copies
-- statement:
--   This statement formalizes the numerical choice of the number of copies in the suspension construction.
--
--   Let $a,\beta,M\in\mathbb R$ satisfy
--   $$a>0,\qquad \beta\ge0,\qquad M\ge0.$$
--   Then there exists an integer $N>0$ such that
--   $$\frac{\beta}{\sqrt N}M\le a.$$
--
--   The result guarantees a positive finite copy number for any positive curvature parameter and finite nonnegative Hessian bound. It is the numerical existence component of the suspension convexity condition.
--
--   **Formalization Note.** The square root uses the real coercion of $N$; the conclusion does not specify a particular choice of $N$.
-- source:
--   Source: Bizeul–Klartag–Lehec, Presenting a proof of the Kannan–Lovász–Simonovits conjecture (arXiv:2610.05474v1), Proposition 7.1, p. 28. Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/BKL/Suspension/Basic.lean#L106-L123 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.BKL.Suspension.Basic`, declaration `FunctionalInequalities.KLS.LogConcave.Suspension.exists_copies`; the repository is private at upload time).

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Bochner_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Calculus
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Gamma
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_IntegrationByParts_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Laplacian
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_BKL_Suspension_Basic
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Measure.Tilted

noncomputable section
open scoped ContDiff
open FunctionalInequalities.Analysis.BakryEmery
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.KLS
end FunctionalInequalities.KLS
open FunctionalInequalities FunctionalInequalities.KLS
section
namespace FunctionalInequalities.KLS.LogConcave
end FunctionalInequalities.KLS.LogConcave
open FunctionalInequalities FunctionalInequalities.KLS FunctionalInequalities.KLS.LogConcave
section
namespace FunctionalInequalities.KLS.LogConcave.Suspension
end FunctionalInequalities.KLS.LogConcave.Suspension
open FunctionalInequalities FunctionalInequalities.KLS FunctionalInequalities.KLS.LogConcave FunctionalInequalities.KLS.LogConcave.Suspension
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem FunctionalInequalities.KLS.LogConcave.Suspension.exists_copies_408915f {a beta M : ℝ} (ha : 0 < a) (hbeta : 0 ≤ beta) (hM : 0 ≤ M) :
    ∃ N : ℕ, 0 < N ∧ beta / Real.sqrt N * M ≤ a := by sorry
