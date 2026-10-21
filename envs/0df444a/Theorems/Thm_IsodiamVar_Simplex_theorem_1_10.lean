-- Prove2me | Theorems.Thm_IsodiamVar_Simplex_theorem_1_10
-- name    : IsodiamVar.Simplex.theorem_1_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:47:18.435689+00:00
-- url     : https://prove2.me/theorems/1ea38887-6da9-4625-92fe-141bcb3506ae
-- title:
--   Theorem 1.10 — sharp isodiametric generalized variance and equality
-- statement:
--   Let $v:[0,\infty)\to[0,\infty)$ be convex and strictly increasing, and set $V(x)=v(\|x\|)$ on $\mathbb R^n$. Let $\mu$ be a Borel probability measure whose support has diameter at most $d\ge0$. With $r_n=\sqrt{n/(2n+2)}$,
--
--   $$
--   \operatorname{Var}_V(\mu)\le v(r_n d).
--   $$
--
--   For $d>0$, if $v$ is differentiable at $r_n d$, equality holds exactly when $\mu$ assigns mass $1/(n+1)$ to each vertex of a regular $n$-simplex of side length $d$. This characterizes every optimizer as well as the sharp bound.
--
--   **Formalization Note** The equality clause adds differentiability at $r_n d$: the printed statement fails for a strictly increasing convex $v$ with a kink there. Strict increase is the interpretation of “increasing” required by the equality claim. Lean uses the extended metric diameter of the support, so an unbounded support cannot satisfy a finite diameter bound; $d\ge0$ keeps the argument of $v$ in its domain.
-- source:
--   Lim & McCann, Geometrical bounds for the variance and recentered moments, arXiv:2001.11851v1, pp. 6–7, Theorem 1.10

import Mathlib
import Definitions.Def_IsodiamVar_Simplex_Defs

open MeasureTheory

namespace IsodiamVar.Simplex

/-- Theorem 1.10, with differentiability at the equality radius. -/
theorem theorem_1_10 (n : ℕ) (v : ℝ → ℝ) (hv0 : ∀ t, 0 ≤ t → 0 ≤ v t)
    (hvconv : ConvexOn ℝ (Set.Ici 0) v) (hvmono : StrictMonoOn v (Set.Ici 0))
    (d : ℝ) (hd : 0 ≤ d) (μ : Measure (E n)) [IsProbabilityMeasure μ]
    (hdiam : EMetric.diam μ.support ≤ ENNReal.ofReal d) :
    varV (fun x => v ‖x‖) μ ≤ v (rn n * d) ∧
      (0 < d → DifferentiableAt ℝ v (rn n * d) →
        (varV (fun x => v ‖x‖) μ = v (rn n * d) ↔
          ∃ x : Fin (n + 1) → E n,
            IsRegularSimplex x d ∧ μ = uniformVertexMeasure x)) := by sorry

end IsodiamVar.Simplex
