-- Prove2me | Theorems.Thm_LanglandsTunnell_TateLocal_exists_rational_clearedFE_finset_sum
-- name    : LanglandsTunnell.TateLocal.exists_rational_clearedFE_finset_sum
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:09.28874+00:00
-- url     : https://prove2.me/theorems/a3fa4150-a075-5ba9-9dd8-897d5a1be56d
-- title:
--   Finite linear combinations preserve rationality and cleared functional equations
-- statement:
--   Fix $q \in \mathbb{C}$ with $q \neq 0$, polynomials $\Gamma_n, \Gamma_d \in \mathbb{C}[X]$ and an integer $e_\Gamma$. Let $S$ be a finite subset of an index type $\iota$, and for each $i \in \iota$ let $c_i \in \mathbb{C}$, let $Z_i, \tilde{Z}_i : \mathbb{C} \to \mathbb{C}$ be functions, let $P_i, \tilde{P}_i, Q_i, \tilde{Q}_i \in \mathbb{C}[X]$, let $m_i, \tilde{m}_i \in \mathbb{Z}$ and $\sigma_i, \tilde{\sigma}_i \in \mathbb{R}$. Assume that for every $i \in S$: $Q_i \neq 0$ and $\tilde{Q}_i \neq 0$; that $Z_i(s)\,Q_i(q^{-s}) = q^{m_i s} P_i(q^{-s})$ whenever $\operatorname{Re} s > \sigma_i$; that $\tilde{Z}_i(s)\,\tilde{Q}_i(q^{-s}) = q^{\tilde{m}_i s} \tilde{P}_i(q^{-s})$ whenever $\operatorname{Re} s > \tilde{\sigma}_i$; and that for all $s \in \mathbb{C}$ the cleared functional equation $q^{\tilde{m}_i s}\tilde{P}_i(q^{-s})\,Q_i(q^{s})\,\Gamma_d(q^{-s}) = \Gamma_n(q^{-s})\,q^{e_\Gamma s}\bigl(q^{-m_i s}P_i(q^{s})\bigr)\tilde{Q}_i(q^{-s})$ holds, all complex powers being $q^{(a:\mathbb{C})s}$ in the `cpow` sense. The conclusion asserts the existence of polynomials $P', \tilde{P}', Q', \tilde{Q}'$ with $Q' \neq 0$, $\tilde{Q}' \neq 0$, integers $m', \tilde{m}'$ and reals $\sigma', \tilde{\sigma}'$ with $\sigma_i \le \sigma'$ and $\tilde{\sigma}_i \le \tilde{\sigma}'$ for all $i \in S$, such that the same three assertions hold with $Z$ replaced by $s \mapsto \sum_{i \in S} c_i Z_i(s)$, $\tilde{Z}$ by $s \mapsto \sum_{i \in S} c_i \tilde{Z}_i(s)$, and the data $(P_i, \tilde{P}_i, Q_i, \tilde{Q}_i, m_i, \tilde{m}_i, \sigma_i, \tilde{\sigma}_i)$ by the primed data — with the very same $\Gamma_n$, $\Gamma_d$ and $e_\Gamma$.
--
--   This is the linearity step for local zeta data in Tate's sense: a finite $\mathbb{C}$-linear combination of local zeta functions which are individually rational in $q^{-s}$ (after clearing denominators) and which satisfy a common functional equation with gamma data $(\Gamma_n, \Gamma_d, e_\Gamma)$ is again of that shape. It feeds [`LanglandsTunnell.TateLocal.exists_gamma_forall_twoVarZeta_rational_and_clearedFE`](thm.html#LanglandsTunnell.TateLocal.exists_gamma_forall_twoVarZeta_rational_and_clearedFE), where the two-variable local functional equation is propagated from individual data to linear combinations of them.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_TateLocal_exists_rational_clearedFE_finset_sum.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem LanglandsTunnell.TateLocal.exists_rational_clearedFE_finset_sum
    (q : ℂ) (hq : q ≠ 0) (Γn Γd : Polynomial ℂ) (eΓ : ℤ)
    {ι : Type*} (S : Finset ι) (c : ι → ℂ) (Z Zd : ι → ℂ → ℂ)
    (P Pd Q Qd : ι → Polynomial ℂ) (m md : ι → ℤ) (σ σd : ι → ℝ)
    (hQ : ∀ i ∈ S, Q i ≠ 0) (hQd : ∀ i ∈ S, Qd i ≠ 0)
    (h1 : ∀ i ∈ S, ∀ s : ℂ, σ i < s.re →
      Z i s * (Q i).eval (q ^ (-s)) = q ^ ((m i : ℂ) * s) * (P i).eval (q ^ (-s)))
    (h2 : ∀ i ∈ S, ∀ s : ℂ, σd i < s.re →
      Zd i s * (Qd i).eval (q ^ (-s)) = q ^ ((md i : ℂ) * s) * (Pd i).eval (q ^ (-s)))
    (h3 : ∀ i ∈ S, ∀ s : ℂ,
      q ^ ((md i : ℂ) * s) * (Pd i).eval (q ^ (-s)) * (Q i).eval (q ^ s) * Γd.eval (q ^ (-s)) =
        Γn.eval (q ^ (-s)) * q ^ ((eΓ : ℂ) * s) * (q ^ ((m i : ℂ) * (-s)) * (P i).eval (q ^ s)) * (Qd i).eval (q ^ (-s))) :
    ∃ (P' Pd' Q' Qd' : Polynomial ℂ) (m' md' : ℤ) (σ' σd' : ℝ), Q' ≠ 0 ∧ Qd' ≠ 0 ∧
      (∀ i ∈ S, σ i ≤ σ' ∧ σd i ≤ σd') ∧
      (∀ s : ℂ, σ' < s.re →
        (∑ i ∈ S, c i * Z i s) * Q'.eval (q ^ (-s)) = q ^ ((m' : ℂ) * s) * P'.eval (q ^ (-s))) ∧
      (∀ s : ℂ, σd' < s.re →
        (∑ i ∈ S, c i * Zd i s) * Qd'.eval (q ^ (-s)) = q ^ ((md' : ℂ) * s) * Pd'.eval (q ^ (-s))) ∧
      (∀ s : ℂ,
        q ^ ((md' : ℂ) * s) * Pd'.eval (q ^ (-s)) * Q'.eval (q ^ s) * Γd.eval (q ^ (-s)) =
          Γn.eval (q ^ (-s)) * q ^ ((eΓ : ℂ) * s) * (q ^ ((m' : ℂ) * (-s)) * P'.eval (q ^ s)) * Qd'.eval (q ^ (-s))) := by sorry
