-- Prove2me | Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_summable_forall_tsum_shell_le_exp_of_norm_le_rpow
-- name    : LanglandsTunnell.RankinSelberg.exists_summable_forall_tsum_shell_le_exp_of_norm_le_rpow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:09.28874+00:00
-- url     : https://prove2.me/theorems/24c70120-5166-5000-ac1e-7766931fee73
-- title:
--   Summable exponential bounds for per-place shell sums
-- statement:
--   Let $S$ be a finite set of finite places of $\mathbb{Q}$, i.e. a finite set of height-one primes of $\mathcal{O}_{\mathbb{Q}}$, let $\lambda,\omega,\lambda',\omega'$ be complex-valued functions on the height-one primes, and let $\kappa$ be real; write $N(v)=\mathrm{absNorm}(v)$ for the absolute norm of the prime ideal $v$. Assume that for every $v\notin S$ all four values satisfy $\|\lambda_v\|,\|\omega_v\|,\|\lambda'_v\|,\|\omega'_v\|\le N(v)^{\kappa}$ (real power). Let $\tau$ be real with $2|\kappa|+4<\tau$. Then there is a function $b$ on the places outside $S$ with $b_v\ge 0$ for all $v$ and $b$ summable, such that for every $v\notin S$ the $[0,\infty]$-valued sum over pairs $(p_1,p_2)\in\mathbb{Z}\times\mathbb{Z}$ of $$N(v)^{p_1-p_2}\,\bigl\|c_v(p_1,p_2)\bigr\|\,\bigl(N(v)^{-(p_1+p_2)}\bigr)^{\tau}$$ (each term pushed into $[0,\infty]$ via `ENNReal.ofReal`) is at most $\exp(b_v)$, where the coefficient $c_v(p_1,p_2)$ is $0$ unless $p_1-p_2\ge 0$ and $p_2\ge 0$, in which case it equals $(\omega_v\omega'_v)^{p_2}\,u_{p_1-p_2}\,u'_{p_1-p_2}$ with $u_m$, $u'_m$ the values at $m=p_1-p_2$ of the sequences determined by $u_0=1$, $u_1=\lambda_v/N(v)$, $u_{m+2}=(\lambda_v u_{m+1}-\omega_v u_m)/N(v)$ and by the same recursion with $(\lambda'_v,\omega'_v)$ in place of $(\lambda_v,\omega_v)$.
--
--   This is the Euler-product convergence input for the finite part of a Rankin–Selberg integral over $\mathbb{Q}$: the bracketed sum is the local factor attached to a place $v$ after the integral has been decomposed into shells indexed by pairs of integers, and the conclusion bounds these factors by exponentials of a summable family, so that their product converges. It is used in [`LanglandsTunnell.RankinSelberg.exists_forall_integrable_finWhittaker_rpow_ideleNorm_det_rat`](thm.html#LanglandsTunnell.RankinSelberg.exists_forall_integrable_finWhittaker_rpow_ideleNorm_det_rat).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_RankinSelberg_exists_summable_forall_tsum_shell_le_exp_of_norm_le_rpow.lean

import Definitions.Def_LanglandsTunnell_RSCarrier
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_LanglandsTunnell_RankinSelbergEuler
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_HaarQuotient
import Definitions.Def_AutomorphicForm_ConstantTerm

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

attribute [local instance] NumberField.AdelicHaar.glBorel

open MeasureTheory NumberField AutomorphicForm IsDedekindDomain UnramifiedWhittaker
open LanglandsTunnell.RankinSelberg

theorem LanglandsTunnell.RankinSelberg.exists_summable_forall_tsum_shell_le_exp_of_norm_le_rpow
    (S : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (lam om lam' om' : HeightOneSpectrum (𝓞 ℚ) → ℂ) (κ : ℝ)
    (hbd : ∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S →
      ‖lam v‖ ≤ ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ κ ∧ ‖om v‖ ≤ ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ κ ∧
      ‖lam' v‖ ≤ ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ κ ∧ ‖om' v‖ ≤ ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ κ)
    (τ : ℝ) (hτ : 2 * |κ| + 4 < τ) :
    ∃ b : {v : HeightOneSpectrum (𝓞 ℚ) // v ∉ S} → ℝ, (∀ v, 0 ≤ b v) ∧ Summable b ∧
      ∀ v : {v : HeightOneSpectrum (𝓞 ℚ) // v ∉ S},
        (∑' p : ℤ × ℤ,
            ENNReal.ofReal
              (((Ideal.absNorm v.1.asIdeal : ℕ) : ℝ) ^ (p.1 - p.2) *
                ‖(if 0 ≤ p.1 - p.2 ∧ 0 ≤ p.2 then
                    (om v.1 * om' v.1) ^ p.2.toNat *
                      heckeRecursionSeq ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) (lam v.1) (om v.1) (p.1 - p.2).toNat *
                      heckeRecursionSeq ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) (lam' v.1) (om' v.1) (p.1 - p.2).toNat
                  else 0)‖ *
                (((Ideal.absNorm v.1.asIdeal : ℕ) : ℝ) ^ (-(p.1 + p.2))) ^ τ)) ≤ ENNReal.ofReal (Real.exp (b v)) := by sorry
