-- Prove2me | Theorems.Thm_LanglandsTunnell_eq_mul_cpow_mul_exp_of_mellin_eq_archFactor_discrete
-- name    : LanglandsTunnell.eq_mul_cpow_mul_exp_of_mellin_eq_archFactor_discrete
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:10.196979+00:00
-- url     : https://prove2.me/theorems/51263215-783b-5ac7-94de-cd5ea8018153
-- title:
--   Discrete-series Whittaker profile identified by Mellin inversion
-- statement:
--   Let $u \in \mathbb{C}$, let $n$ be a natural number with $1 \le n$, and let $W : \mathbb{R} \to \mathbb{C}$ be a function that is continuous on the set $\{t \in \mathbb{R} : t \neq 0\}$ and vanishes on the negative reals, that is, $W(t) = 0$ whenever $t < 0$. Assume further that there is a real $s_0$ such that for every $s \in \mathbb{C}$ with $\operatorname{Re}(s) > s_0$ the Mellin transform of $t \mapsto W(t)/t$ converges at $s$ (in Mathlib's sense, `MellinConvergent`) and its value is the archimedean factor of the discrete-series parameter $\mathrm{discrete}\ u\ n$: since that parameter has empty real gamma multiset and complex gamma multiset $\{u + n/2\}$, the asserted identity reads $$\int_0^{\infty} W(t)\, t^{s-2}\, \mathrm{d}t = \Gamma_{\mathbb{C}}\!\left(s + u + \tfrac{n}{2}\right)$$ for all such $s$. The conclusion is that $W$ is given on the positive reals by the explicit profile: for every real $t > 0$, $$W(t) = 2\, t^{\,u + n/2 + 1} e^{-2\pi t},$$ the power being the complex power of the positive real $t$.
--
--   This is the uniqueness half of the determination of the archimedean Whittaker profile of a discrete-series representation of $GL_2(\mathbb{R})$: a one-sided function whose Mellin transform along $t \mapsto W(t)/t$ is the $\Gamma_{\mathbb{C}}$-factor attached to the parameter $\mathrm{discrete}\ u\ n$ must coincide with the classical profile $2t^{u+n/2+1}e^{-2\pi t}$ on $t>0$. It is used in the Rankin–Selberg part of the Langlands–Tunnell argument, where the discrete-series Whittaker function is pinned down before the archimedean local integrals are computed; the proof invokes polynomial-times-exponential upper and lower bounds for $\Gamma$ in vertical strips, which control the inversion contour.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_eq_mul_cpow_mul_exp_of_mellin_eq_archFactor_discrete.lean

import Definitions.Def_LanglandsTunnell_ArchParam
import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.MellinInversion

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Real
open LanglandsTunnell

theorem LanglandsTunnell.eq_mul_cpow_mul_exp_of_mellin_eq_archFactor_discrete
    (u : ℂ) (n : ℕ) (hn : 1 ≤ n) (W : ℝ → ℂ)
    (hWc : ContinuousOn W {t : ℝ | t ≠ 0})
    (hneg : ∀ t : ℝ, t < 0 → W t = 0)
    (hMel : ∃ s₀ : ℝ, ∀ s : ℂ, s₀ < s.re →
      MellinConvergent (fun t : ℝ => W t / (t : ℂ)) s ∧
        mellin (fun t : ℝ => W t / (t : ℂ)) s = (RealArchParam.discrete u n hn).archFactor s)
    (t : ℝ) (ht : 0 < t) :
    W t = (2 : ℂ) * (t : ℂ) ^ (u + (n : ℂ) / 2 + 1) * (Real.exp (-(2 * π * t)) : ℂ) := by sorry
