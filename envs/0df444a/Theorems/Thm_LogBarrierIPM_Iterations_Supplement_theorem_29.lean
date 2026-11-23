-- Prove2me | Theorems.Thm_LogBarrierIPM_Iterations_Supplement_theorem_29
-- name    : LogBarrierIPM.Iterations.Supplement.theorem_29
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T17:27:33.187229+00:00
-- url     : https://prove2.me/theorems/f246ccfe-0291-4ee4-98e2-cd9f26c248ed
-- title:
--   Theorem 29 — general polygonal bound (corrected: separated subintervals)
-- statement:
--   Assume Assumption 13 and $N\ge1$. Fix $0<\theta<1$, an optimal pair with a Lemma 18 threshold $t_0$, and any $t_1\ge\max(t_0,1)$ such that $\varepsilon_t=\log_t(2N/(1-\theta))+\delta(t)<\varepsilon_0$ for every $t>t_1$. Let $t>t_1$ and let a polygonal curve of $p\ge1$ segments lie in the wide neighborhood. Let $a\le b$ be any subinterval of the closed interval between the logarithmic duality measures of the curve's first and last points, in either order. If every vertex parameter $v\in(a,b)$ satisfies
--   $$d_\infty(C^{\rm trop}(a),C^{\rm trop}(v))>2\varepsilon_t,\qquad d_\infty(C^{\rm trop}(b),C^{\rm trop}(v))>4\varepsilon_t,$$
--   then
--   $$p\ge\gamma([a,b]).$$
--   This gives the printed bound when the two end levels are separated, and it still bounds curves whose end levels are near vertices through an interior subinterval. The printed theorem is false: for $n=m=2$, $A=I$, $b=(1,t^2)$, $c=(1,1)$, every $t>t_1$ and small $\eta>0$, the segment between the central points of parameters $t^{-\eta}$ and $t^{\eta}$ lies in the neighborhood, so $p=1$, while $\gamma([-\eta,\eta])=2$.
--
--   Differences from the source:
--   - correction: the endpoint interval always gives p≥γ → every subinterval [a,b] of the endpoint-level range, in either orientation, with interior vertices at distance >2ε_t from a and >4ε_t from b; reason: apply the repaired Proposition 28 after cutting at the two levels; without separation the A=I example has one real segment across a tropical breakpoint
--   - correction: the displayed dual says maximize bᵀy → minimize bᵀy, equivalently maximize -bᵀy; reason: the gap on pp. 14–15 is cᵀx+bᵀy; Proposition 14 uses bᵀy+ν≥0, and the central-path barrier on p. 4 already has -bᵀy
--   - encoding: the threshold (35) and a positive-segment polygonal curve → t1≥max(t0,1), p≥1 and N≥1, with extended distances and a least positive segment count; reason: logarithms have increasing base, μ̄ is defined, and neither infinite distance nor an empty infimum is converted to zero
--   - encoding: the value t0 kept from Lemma 18 → any t0 with the three properties of Lemma 18, beyond the convergence radii; reason: the evaluated programs are defined only there (p. 8)
--   - encoding: relations over the ordered field K → eventual relations between evaluations of the published convergent series; reason: p. 7 identifies order and equality with eventual evaluations; no domain is restricted
--   - encoding: the point C^trop(λ) of T^{2N}, indexed from 1 → a real vector indexed by Fin ((n+m)+(n+m)), in the order x, w, s, y; reason: under Assumption 13 all coordinates are finite by (20); Theorem 15 asserts that this vector is the barycenter
-- source:
--   Allamigeon, Benchimol, Gaubert, Joswig, Log-Barrier Interior Point Methods Are Not Strongly Polynomial, arXiv:1708.01544v2, p. 26, Theorem 29

import Mathlib
import Definitions.Def_LogBarrierIPM_Iterations_Supplement_TropicalTube

open Filter Matrix

namespace LogBarrierIPM.Iterations.Supplement
open LogBarrierIPM.Curvature

theorem theorem_29 {m n : ℕ} (A : Matrix (Fin m) (Fin n) Puiseux)
    (b : Fin m → Puiseux) (c : Fin n → Puiseux)
    (hstrict : StrictlyFeasibleK A b c)
    (hN : 1 ≤ n + m)
    (zstar : PuiseuxSlackPoint n m) (hopt : OptimalPairK A b c zstar)
    (t0 : ℝ) (ht0 : SpecializationThreshold A b c zstar t0)
    (θ : ℝ) (hθ : 0 < θ ∧ θ < 1)
    (t1 : ℝ) (ht1 : TubeThreshold A b c θ t0 t1) (t : ℝ) (ht : t1 < t)
    (p : ℕ) (hp : 1 ≤ p) (z : Fin (p + 1) → PDPoint n m)
    (hcontained : ∀ i : Fin p, segment ℝ (z i.castSucc) (z i.succ) ⊆
      wideNeighborhood (evalMatrix A t) (evalFun b t) (evalFun c t) θ)
    (a b' : ℝ) (hab : a ≤ b')
    (halevel : min (Real.logb t (dualityMeasure (z 0)))
      (Real.logb t (dualityMeasure (z (Fin.last p)))) ≤ a)
    (hblevel : b' ≤ max (Real.logb t (dualityMeasure (z 0)))
      (Real.logb t (dualityMeasure (z (Fin.last p)))))
    (hsep : EndpointsSeparated (tropicalPath A b c) a b' (epsilonAt A b c θ t)) :
    gamma (tropicalPath A b c) a b' ≤ (p : WithTop ℕ) := by sorry

end LogBarrierIPM.Iterations.Supplement
