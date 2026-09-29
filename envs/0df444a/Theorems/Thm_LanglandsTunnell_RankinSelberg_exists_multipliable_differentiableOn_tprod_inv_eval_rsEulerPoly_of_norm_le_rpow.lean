-- Prove2me | Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_multipliable_differentiableOn_tprod_inv_eval_rsEulerPoly_of_norm_le_rpow
-- name    : LanglandsTunnell.RankinSelberg.exists_multipliable_differentiableOn_tprod_inv_eval_rsEulerPoly_of_norm_le_rpow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.680094+00:00
-- url     : https://prove2.me/theorems/ec18fdeb-84ea-5c06-85cf-baeee2bf5688
-- title:
--   Convergence of the Rankin–Selberg GL₂timesGL₂ Euler product
-- statement:
--   Let $K$ be a number field, let $S$ be a finite set of height-one primes of the ring of integers $\mathcal{O}_K$, let $a,b,a',b'$ be complex-valued functions on the subtype of height-one primes $v \notin S$, and let $\kappa$ be a real number. Assume that for every such $v$ the four values $a_v, b_v, a'_v, b'_v$ all have absolute value at most $N(v)^{\kappa}$, where $N(v)$ is the absolute norm of the ideal $v$ and the power is a real power. Then there exists a real number $\sigma_0$ with the following three properties. First, for every $s \in \mathbb{C}$ with $\operatorname{Re} s > \sigma_0$, the family indexed by the primes $v \notin S$ of reciprocals of $P_v(N(v)^{-s})$ is multipliable, where $N(v)^{-s}$ is the complex power and $$P_v(X) = 1 - a_v a'_v X + (a_v^2 b'_v + b_v a'^2_v - 2 b_v b'_v)X^2 - a_v b_v a'_v b'_v X^3 + b_v^2 b'^2_v X^4$$ is the polynomial obtained from `rsEulerPoly` evaluated at the data $(a_v, b_v, a'_v, b'_v)$ with its fifth argument set to $0$ (so the degree-$6$ terms of that definition drop out). Second, the function $s \mapsto \prod'_{v \notin S} P_v(N(v)^{-s})^{-1}$ is complex-differentiable on the half-plane $\{\operatorname{Re} s > \sigma_0\}$. Third, this unconditional product is nonzero at every $s$ with $\operatorname{Re} s > \sigma_0$. No explicit value of $\sigma_0$ is asserted.
--
--   This provides a half-plane of absolute convergence, holomorphy and non-vanishing for the partial Rankin–Selberg Euler product $L^S(s,\pi\times\pi')$ attached to two polynomially bounded systems of $\mathrm{GL}_2$ Hecke data over $K$, the degree-four local factors being the $\mathrm{GL}_2\times\mathrm{GL}_2$ Rankin–Selberg polynomials in the Satake parameters. It is used in the construction of the Rankin–Selberg integrals comparing Petersson products with Euler products, and is deduced from the degree-one statement [`NumberField.multipliable_differentiableOn_tprod_ne_zero_eulerProduct_of_norm_le_one`](thm.html#NumberField.multipliable_differentiableOn_tprod_ne_zero_eulerProduct_of_norm_le_one).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_RankinSelberg_exists_multipliable_differentiableOn_tprod_inv_eval_rsEulerPoly_of_norm_le_rpow.lean

import Mathlib.Analysis.Complex.Basic
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Definitions.Def_LanglandsTunnell_RankinSelbergEuler

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField

theorem LanglandsTunnell.RankinSelberg.exists_multipliable_differentiableOn_tprod_inv_eval_rsEulerPoly_of_norm_le_rpow
    (K : Type) [Field K] [NumberField K] (S : Finset (HeightOneSpectrum (𝓞 K)))
    (a b a' b' : {v : HeightOneSpectrum (𝓞 K) // v ∉ S} → ℂ) (κ : ℝ)
    (hbd : ∀ v, ‖a v‖ ≤ ((Ideal.absNorm v.1.asIdeal : ℕ) : ℝ) ^ κ ∧ ‖b v‖ ≤ ((Ideal.absNorm v.1.asIdeal : ℕ) : ℝ) ^ κ ∧
      ‖a' v‖ ≤ ((Ideal.absNorm v.1.asIdeal : ℕ) : ℝ) ^ κ ∧ ‖b' v‖ ≤ ((Ideal.absNorm v.1.asIdeal : ℕ) : ℝ) ^ κ) :
    ∃ σ₀ : ℝ,
      (∀ s : ℂ, σ₀ < s.re →
        Multipliable (fun v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S} =>
          ((LanglandsTunnell.RankinSelberg.rsEulerPoly (a v) (b v) (a' v) (b' v) 0).eval
            (((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s)))⁻¹)) ∧
      DifferentiableOn ℂ (fun s : ℂ => ∏' v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S},
          ((LanglandsTunnell.RankinSelberg.rsEulerPoly (a v) (b v) (a' v) (b' v) 0).eval
            (((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s)))⁻¹) {s : ℂ | σ₀ < s.re} ∧
      (∀ s : ℂ, σ₀ < s.re →
        (∏' v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S},
          ((LanglandsTunnell.RankinSelberg.rsEulerPoly (a v) (b v) (a' v) (b' v) 0).eval
            (((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s)))⁻¹) ≠ 0) := by sorry
