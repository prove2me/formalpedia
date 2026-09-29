-- Prove2me | Theorems.Thm_LanglandsTunnell_RankinSelberg_forall_cleared_fe_of_laurent_fe_of_rational_forms
-- name    : LanglandsTunnell.RankinSelberg.forall_cleared_fe_of_laurent_fe_of_rational_forms
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:09.28874+00:00
-- url     : https://prove2.me/theorems/43f1a179-0440-58ab-b674-0ee2fa3704e1
-- title:
--   Transfer of a Laurent functional equation to cleared rational forms
-- statement:
--   Fix an integer $q$ with $1<q$ and three functions $Z,Z^{\vee},\gamma:\mathbb{C}\to\mathbb{C}$. Assume a first, "Laurent", description: complex polynomials $P_0,P_0^{\vee}$, integers $m_0,m_0^{\vee}$ and reals $\sigma_0,\sigma_0^{\vee}$ such that $Z(s)=q^{m_0 s}P_0(q^{-s})$ whenever $\operatorname{Re}s>\sigma_0$, and $Z^{\vee}(s)=q^{m_0^{\vee}s}P_0^{\vee}(q^{-s})$ whenever $\operatorname{Re}s>\sigma_0^{\vee}$, together with the functional equation $q^{m_0^{\vee}s}P_0^{\vee}(q^{-s})=\gamma(s)\bigl(q^{m_0(-s)}P_0(q^{s})\bigr)$ for all $s\in\mathbb{C}$ (not merely on a half-plane). Assume also a second, "rational", description: complex polynomials $P,P^{\vee},Q,Q^{\vee}$ with $Q\neq 0$ and $Q^{\vee}\neq 0$, integers $m,m^{\vee}$ and reals $\sigma,\sigma^{\vee}$ such that $Z(s)Q(q^{-s})=q^{ms}P(q^{-s})$ for $\operatorname{Re}s>\sigma$ and $Z^{\vee}(s)Q^{\vee}(q^{-s})=q^{m^{\vee}s}P^{\vee}(q^{-s})$ for $\operatorname{Re}s>\sigma^{\vee}$. The conclusion is the cleared functional equation for the second description, valid at every $s\in\mathbb{C}$: $$q^{m^{\vee}s}P^{\vee}(q^{-s})\,Q(q^{s})=\gamma(s)\bigl(q^{m(-s)}P(q^{s})\bigr)\,Q^{\vee}(q^{-s}).$$ Here all powers are complex powers of the real number $q$, and the same $\gamma$ occurs in hypothesis and conclusion.
--
--   This is the bookkeeping step that converts the local Rankin–Selberg functional equation from its existential Laurent-polynomial shape, one pair $(P_0,m_0)$, $(P_0^{\vee},m_0^{\vee})$ at a time, into the cleared shape quantified over all rational presentations $Z\cdot Q=q^{ms}P$ of the same pair of local integrals, in which the $\gamma$-factor statements are phrased. It is used in assembling the functional equation for the local $GL_3\times GL_2$ integrals on spans of Whittaker vectors.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_RankinSelberg_forall_cleared_fe_of_laurent_fe_of_rational_forms.lean

import Mathlib
import Theorems.Thm_Complex_forall_cpow_mul_eval_mul_eval_eq_and_exists_finset_forall_eq_mul_of_infinite

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem LanglandsTunnell.RankinSelberg.forall_cleared_fe_of_laurent_fe_of_rational_forms
    (q : ℕ) (hq : 1 < q) (Z Zd γ : ℂ → ℂ)

    (P₀ Pd₀ : Polynomial ℂ) (m₀ md₀ : ℤ) (σ₀ σd₀ : ℝ)
    (hZ₀ : ∀ s : ℂ, σ₀ < s.re → Z s = (q : ℂ) ^ ((m₀ : ℂ) * s) * P₀.eval ((q : ℂ) ^ (-s)))
    (hZd₀ : ∀ s : ℂ, σd₀ < s.re → Zd s = (q : ℂ) ^ ((md₀ : ℂ) * s) * Pd₀.eval ((q : ℂ) ^ (-s)))
    (hFE₀ : ∀ s : ℂ, (q : ℂ) ^ ((md₀ : ℂ) * s) * Pd₀.eval ((q : ℂ) ^ (-s)) =
      γ s * ((q : ℂ) ^ ((m₀ : ℂ) * (-s)) * P₀.eval ((q : ℂ) ^ s)))

    (P Pd Q Qd : Polynomial ℂ) (m md : ℤ) (σ σd : ℝ) (hQ : Q ≠ 0) (hQd : Qd ≠ 0)
    (hZ : ∀ s : ℂ, σ < s.re → Z s * Q.eval ((q : ℂ) ^ (-s)) = (q : ℂ) ^ ((m : ℂ) * s) * P.eval ((q : ℂ) ^ (-s)))
    (hZd : ∀ s : ℂ, σd < s.re →
      Zd s * Qd.eval ((q : ℂ) ^ (-s)) = (q : ℂ) ^ ((md : ℂ) * s) * Pd.eval ((q : ℂ) ^ (-s))) :
    ∀ s : ℂ, (q : ℂ) ^ ((md : ℂ) * s) * Pd.eval ((q : ℂ) ^ (-s)) * Q.eval ((q : ℂ) ^ s) =
      γ s * ((q : ℂ) ^ ((m : ℂ) * (-s)) * P.eval ((q : ℂ) ^ s)) * Qd.eval ((q : ℂ) ^ (-s)) := by sorry
