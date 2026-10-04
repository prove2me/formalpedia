-- Prove2me | Theorems.Thm_NumStochOpt_Bounds_eq_2_30_2_31_dual_multiplier_lower_bound
-- name    : NumStochOpt.Bounds.eq_2_30_2_31_dual_multiplier_lower_bound
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-30T19:07:29.458983+00:00
-- url     : https://prove2.me/theorems/17e15f46-88f3-431b-ba67-2a6c73cc95e5
-- title:
--   Eqs. (2.30)–(2.31) — lower bound by dual multipliers
-- statement:
--   Consider the two-stage problem with complete recourse matrix $W$, deterministic cost vector $q$, first-stage cost $c$, and random $h(\omega)$, $T(\omega)$ on a probability space $(\Omega,P)$ whose components are integrable. Let $u_1,\dots,u_L\in\mathbb R^{m_2}$, $L\ge1$, be feasible for the dual of the second-stage problem, $W^Tu_\ell\le q$. Fix $x\in\mathbb R^{n_1}$. Then for every $\omega$
--   $$
--   Q(x,\xi(\omega))\;\ge\;\max_{1\le\ell\le L}\big(h(\omega)-T(\omega)x\big)^Tu_\ell, \tag{2.30}
--   $$
--   and, taking expectations,
--   $$
--   \psi(x)=c^Tx+\int_\Omega Q(x,\xi(\omega))\,P(d\omega)\;\ge\;c^Tx+E\Big\{\max_{1\le\ell\le L}\big(h(\omega)-T(\omega)x\big)^Tu_\ell\Big\}. \tag{2.31}
--   $$
--
--   Because $q$ is deterministic, the same multipliers are dual feasible for every realization; the bound approximates $Q(x,\cdot)$ from below by a convex piecewise linear function.
--
--   **Formalization Note** The book names the right-hand sides $\tilde Q(x,\xi(\omega))$ and $\tilde\psi(x)$, names it already used for the different functions of (2.27); in Lean the minorant is `dualLowerBound`. Integrability of $h$ and $T$ is assumed so that $\psi(x)$ and the right-hand side of (2.31) are finite, which the book presupposes; the standing complete-recourse assumption (p. 40) is carried.
-- source:
--   P. Kall, A. Ruszczyński, K. Frauendorfer, "Approximation Techniques in Stochastic Programming", in Ermoliev & Wets (eds.), Numerical Techniques for Stochastic Optimization, Springer 1988, Ch. 2, p. 43, Eqs. (2.30)-(2.31)

import Mathlib
import Definitions.Def_NumStochOpt_Bounds_RecourseCost

open MeasureTheory Matrix

namespace NumStochOpt.Bounds

/-- Eqs. (2.30)–(2.31), p. 43: with deterministic `q` and dual-feasible multipliers
`u_1, …, u_L` (`Wᵀ u_ℓ ≤ q`), pointwise `Q(x, ξ(ω)) ≥ max_ℓ (h(ω) − T(ω) x)ᵀ u_ℓ`, and taking
expectations `ψ(x) = cᵀx + E Q(x, ξ) ≥ cᵀx + E max_ℓ (h(ω) − T(ω) x)ᵀ u_ℓ`. -/
theorem eq_2_30_2_31_dual_multiplier_lower_bound {Ω ι κ ν : Type*} [MeasurableSpace Ω]
    [Fintype ι] [Fintype κ] [Fintype ν] (P : Measure Ω) [IsProbabilityMeasure P]
    (W : Matrix ι κ ℝ) (hW : CompleteRecourse W) (c : ν → ℝ) (q : κ → ℝ)
    (h : Ω → ι → ℝ) (T : Ω → Matrix ι ν ℝ)
    (hh : ∀ i, Integrable (fun ω => h ω i) P) (hT : ∀ i j, Integrable (fun ω => T ω i j) P)
    {L : ℕ} [NeZero L] (u : Fin L → ι → ℝ) (hu : ∀ ℓ, W.transpose *ᵥ u ℓ ≤ q) (x : ν → ℝ) :
    (∀ ω, ((dualLowerBound u (h ω) (T ω) x : ℝ) : EReal) ≤ recourseCost W q (h ω) (T ω) x) ∧
      c ⬝ᵥ x + ∫ ω, dualLowerBound u (h ω) (T ω) x ∂P ≤
        c ⬝ᵥ x + expectedRecourse P W (fun _ => q) h T x := by sorry

end NumStochOpt.Bounds
