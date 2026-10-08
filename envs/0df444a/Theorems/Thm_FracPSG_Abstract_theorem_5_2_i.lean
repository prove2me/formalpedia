-- Prove2me | Theorems.Thm_FracPSG_Abstract_theorem_5_2_i
-- name    : FracPSG.Abstract.theorem_5_2_i
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T21:08:55.762981+00:00
-- url     : https://prove2.me/theorems/61e7975e-0dbb-4035-80d5-3d1f5ce17c54
-- title:
--   Theorem 5.2(i) — finite length of (Δₙ)
-- statement:
--   Suppose (H1), (H2), (H3) and (H4) hold, $(z_n)$ is bounded, and $h$ is constant on the set $\Omega$ of cluster points of $(z_n)$ and has the KL property at each point of $\Omega$. Then
--   $$\sum_{n=0}^{+\infty}\Delta_n<+\infty .$$
--
--   This is the finite-length property of the abstract framework, from which convergence of any sequence tied to $(\Delta_n)$ by (H5) follows.
--
--   **Formalization Note** For the nonnegative sequence $\Delta_n$, finiteness of the series is `Summable`. Conventions as in the definitions file.
-- source:
--   Boţ, Dao, Li, Extrapolated Proximal Subgradient Algorithms for Nonconvex and Nonsmooth Fractional Programs, arXiv:2003.04124v2, p. 15, Theorem 5.2(i)

import Mathlib
import Definitions.Def_NonconvexSplitting_Shared_StandingAssumptions
import Definitions.Def_NonconvexSplitting_Shared_LimitingSubdiff
import Definitions.Def_NonconvexSplitting_ADMMKL_KLProperty
import Definitions.Def_FracPSG_Abstract_Basic

open Filter Topology

namespace FracPSG.Abstract

open NonconvexSplitting.Shared NonconvexSplitting.ADMMKL

/-- Theorem 5.2(i) (Boţ–Dao–Li, arXiv:2003.04124v2, p. 15): under (H1)–(H4), with `(zₙ)` bounded and
`h` constant on the set `Ω` of cluster points and having the KL property at each point of `Ω`,
`∑_{n ≥ 0} Δₙ < +∞`. -/
theorem theorem_5_2_i {P : ℕ} {h : EuclideanSpace ℝ (Fin P) → EReal}
    {z : ℕ → EuclideanSpace ℝ (Fin P)} {α β ε : ℕ → ℝ} {Δ : ℤ → ℝ} {ilo ihi : ℤ}
    {lam : ℤ → ℝ}
    (hset : AbstractSetting h α β ε Δ ilo ihi lam)
    (hH1 : H1 h z α Δ) (hH2 : H2 h z β ε Δ ilo ihi lam) (hH3 : H3 h z) (hH4 : H4 α β ε)
    (hbdd : Bornology.IsBounded (Set.range z))
    (hconst : ∀ z₁ ∈ clusterSet z, ∀ z₂ ∈ clusterSet z, h z₁ = h z₂)
    (hKL : ∀ zbar ∈ clusterSet z, HasKLProperty h zbar) :
    Summable (fun n : ℕ => Δ n) := by sorry

end FracPSG.Abstract
