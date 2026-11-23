-- Prove2me | Theorems.Thm_LogBarrierIPM_Iterations_Supplement_theorem_19
-- name    : LogBarrierIPM.Iterations.Supplement.theorem_19
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T17:24:50.200977+00:00
-- url     : https://prove2.me/theorems/99bfec12-21b8-4d57-8685-ef3ae9207343
-- title:
--   Theorem 19 — uniform wide-neighborhood approximation (corrected: dual sign in the definition of t₀)
-- statement:
--   Assume Assumption 13, let $N=n+m\ge1$, fix $0<\theta<1$ and an optimal pair, and let $t_0$ be any specialization threshold of Lemma 18. For every $t>t_0$ with $t>1$ and every $\mu>0$,
--   $$d_\infty\bigl(\log_t N^{-\infty}_{\theta,t}(\mu),C^{\rm trop}(\log_t\mu)\bigr)\le\log_t\!\left(\frac{N}{1-\theta}\right)+\delta(t).$$
--   The neighborhood slice uses the published duality measure and wide neighborhood. The distance is directed to the singleton central point, and $\delta(t)=2d_H(\log_t\mathcal F(t),\operatorname{val}(\mathcal F))$ may be infinite. The estimate is uniform in $\mu$; neither the constant nor the error term is replaced by a qualitative limit.
--
--   Differences from the source:
--   - correction: the displayed dual says maximize bᵀy → minimize bᵀy, equivalently maximize -bᵀy; reason: the gap on pp. 14–15 is cᵀx+bᵀy; Proposition 14 uses bᵀy+ν≥0, and the central-path barrier on p. 4 already has -bᵀy
--   - encoding: base-t logarithms and division by N → t>1 and N≥1; reason: these exclude the undefined zero-dimensional measure and the non-increasing or undefined logarithmic bases; they are the standing conventions of (2) and (13)
--   - encoding: 1-based finite vectors and the tropical semiring → 0-based Fin vectors and WithBot real coordinates; reason: the index shift preserves every coordinate, including bottom values
--   - encoding: the value t0 kept from Lemma 18 → any t0 with the three properties of Lemma 18, beyond the convergence radii of the data and of the optimal pair; reason: the evaluated programs are defined only there (p. 8), and Lemma 18 supplies such a value
--   - encoding: directed distance to a point, and δ(t) → extended-real distance to the singleton, with δ(t) possibly +∞; reason: no infinite or empty supremum is replaced by a real default
--   - encoding: relations over the ordered field K → eventual relations between evaluations of the published convergent series; reason: p. 7 identifies order and equality with eventual evaluations; no domain is restricted
-- source:
--   Allamigeon, Benchimol, Gaubert, Joswig, Log-Barrier Interior Point Methods Are Not Strongly Polynomial, arXiv:1708.01544v2, p. 17, Theorem 19

import Mathlib
import Definitions.Def_LogBarrierIPM_Iterations_Supplement_Specialization

open Filter Matrix

namespace LogBarrierIPM.Iterations.Supplement
open LogBarrierIPM.Curvature

theorem theorem_19 {m n : ℕ} (A : Matrix (Fin m) (Fin n) Puiseux)
    (b : Fin m → Puiseux) (c : Fin n → Puiseux)
    (hstrict : StrictlyFeasibleK A b c)
    (hN : 1 ≤ n + m)
    (zstar : PuiseuxSlackPoint n m) (hopt : OptimalPairK A b c zstar)
    (t0 : ℝ) (ht0 : SpecializationThreshold A b c zstar t0)
    (θ : ℝ) (hθ : 0 < θ ∧ θ < 1)
    (t : ℝ) (ht : t0 < t) (htbase : 1 < t) (μ : ℝ) (hμ : 0 < μ) :
    hausdorffInf (logImage t (neighborhoodSlice A b c θ t μ))
      {tropicalizeReal (tropicalPath A b c (Real.logb t μ))} ≤
    (Real.logb t ((n + m : ℕ) / (1 - θ)) : EReal) + delta A b c t := by sorry

end LogBarrierIPM.Iterations.Supplement
