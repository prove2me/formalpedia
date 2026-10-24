-- Prove2me | Theorems.Thm_FunctionalInequalities_KLS_LogConcave_Suspension_convexOn_potential_408915f
-- name    : FunctionalInequalities.KLS.LogConcave.Suspension.convexOn_potential_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T14:37:28.624679+00:00
-- url     : https://prove2.me/theorems/c66c6b44-0aee-412e-9724-da286bb5e27e
-- title:
--   Convexity of the Finite-Copy Suspension Potential
-- statement:
--   This auxiliary convexity statement formalizes the convexity component of Proposition 7.1, p. 28, equations (109)–(110), of Bizeul–Klartag–Lehec (arXiv:2610.05474v1).
--
--   Let $E$ be a real inner product space and let $V,f:E\to\mathbb R$ be $C^2$. Let $a,M,\beta,\sigma\in\mathbb R$ and $N\in\mathbb N$. Assume:
--   1. $\beta\ge0$.
--   2. $D^2V(x)[v,v]\ge a\|v\|^2$ for every $x,v\in E$, with the bilinear second derivative represented by `bilinearIteratedFDerivTwo`.
--   3. $\|D(Df)(x)\|\le M$ for every $x\in E$, using `fderiv` and its operator norm.
--   4. $(\beta/\sqrt N)M\le a$.
--
--   The function defined by `potential`,
--   $$
--   W_N(s,x)=\sum_{i\in\operatorname{Fin}N}V(x_i)+\beta\left|\sigma s-\frac{\sum_i f(x_i)}{\sqrt N}\right|,
--   $$
--   is convex on all of $\mathbb R\times(\operatorname{Fin}N\to E)$.
--
--   This isolates the deterministic convexity condition used in the suspension construction, rather than the full proposition.
--
--   **Formalization Note** No positivity restriction on $N$, $a$, $M$, or $\sigma$ is added. In particular $N=0$ is allowed, with Lean's totalized real division.
-- source:
--   Source: Bizeul–Klartag–Lehec, Presenting a proof of the Kannan–Lovász–Simonovits conjecture (arXiv:2610.05474v1), Proposition 7.1, p. 28. Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/BKL/Suspension/Basic.lean#L83-L104 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.BKL.Suspension.Basic`, declaration `FunctionalInequalities.KLS.LogConcave.Suspension.convexOn_potential`; the repository is private at upload time).

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

theorem FunctionalInequalities.KLS.LogConcave.Suspension.convexOn_potential_408915f {V f : E → ℝ} (hV : ContDiff ℝ 2 V) (hf : ContDiff ℝ 2 f)
    {a M beta sigma : ℝ} (hbeta : 0 ≤ beta)
    (hVlower : ∀ x v, a * ‖v‖ ^ 2 ≤ bilinearIteratedFDerivTwo ℝ V x v v)
    (hfbound : ∀ x, ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ M)
    (N : ℕ) (hN : beta / Real.sqrt N * M ≤ a) :
    ConvexOn ℝ Set.univ (potential V f beta sigma N) := by sorry
