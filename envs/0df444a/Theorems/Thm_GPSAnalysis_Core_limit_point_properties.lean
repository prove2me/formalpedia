-- Prove2me | Theorems.Thm_GPSAnalysis_Core_limit_point_properties
-- name    : GPSAnalysis.Core.limit_point_properties
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T07:34:03.803718+00:00
-- url     : https://prove2.me/theorems/8af53f70-d4f4-4d1b-9c81-0ff514d4d534
-- title:
--   Theorem 3.1 — limit points of GPS iterates and the limit of $f(x_k)$
-- statement:
--   Consider a GPS run $\{x_k\}$ on problem (1.1) satisfying A1 ($f_\Omega(x_0)<\infty$) and A3 (all iterates lie in a compact set). Then:
--
--   1. the sequence $\{x_k\}$ has at least one limit point (cluster point);
--   2. if $f$ is lower semicontinuous at a limit point $\bar x$, then $\lim_k f(x_k)$ exists, is finite, and
--   $$\lim_{k\to\infty} f(x_k)\ \ge\ f(\bar x);$$
--   3. if $f$ is continuous at every limit point of $\{x_k\}$, then all limit points have the same function value.
--
--   The result needs no smoothness at all: it rests on the fact that GPS never increases $f_\Omega$. It shows that all limit points at which $f$ is continuous are equally good in function value.
--
--   **Formalization Note** $f$ takes values in $\mathbb R\cup\{+\infty\}$ with its order topology; lower semicontinuity and continuity are those of $f$, not of $f_\Omega$. The limit is asserted to be a real number.
-- source:
--   Audet, Dennis, Analysis of Generalized Pattern Searches, SIAM J. Optim. 13 (2003), p. 894, Theorem 3.1

import Mathlib
import Definitions.Def_GPSAnalysis_Core_Problem
import Definitions.Def_GPSAnalysis_Core_Mesh
import Definitions.Def_GPSAnalysis_Core_Run

open Filter Topology

namespace GPSAnalysis.Core

/-- Theorem 3.1 (Audet–Dennis 2003, p. 894). Under A1 and A3 the iterate sequence has a limit
point; if `f` is lower semicontinuous at a limit point `x̄`, then `lim_k f(x_k)` exists (finite)
and is `≥ f(x̄)`; if `f` is continuous at every limit point, all limit points have the same value. -/
theorem limit_point_properties {n m p : ℕ} (P : GPSSetup n m p) (R : GPSRun P)
    (hA1 : AssumptionA1 R) (hA3 : AssumptionA3 R) :
    (∃ xbar : Fin n → ℝ, MapClusterPt xbar atTop R.x) ∧
    (∀ xbar : Fin n → ℝ, MapClusterPt xbar atTop R.x → LowerSemicontinuousAt P.f xbar →
      ∃ ℓ : ℝ, Tendsto (fun k => P.f (R.x k)) atTop (𝓝 (ℓ : WithTop ℝ)) ∧
        P.f xbar ≤ (ℓ : WithTop ℝ)) ∧
    ((∀ xbar : Fin n → ℝ, MapClusterPt xbar atTop R.x → ContinuousAt P.f xbar) →
      ∀ x₁ x₂ : Fin n → ℝ, MapClusterPt x₁ atTop R.x → MapClusterPt x₂ atTop R.x →
        P.f x₁ = P.f x₂) := by sorry

end GPSAnalysis.Core
