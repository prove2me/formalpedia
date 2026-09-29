-- Prove2me | Theorems.Thm_ModularForm_exists_gammaH_apply_mul_apply_ne_of_forall_smul_ne_of_gamma0_smul_eq
-- name    : ModularForm.exists_gammaH_apply_mul_apply_ne_of_forall_smul_ne_of_gamma0_smul_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.335791+00:00
-- url     : https://prove2.me/theorems/3a10524d-6b82-524d-90d0-70877972722b
-- title:
--   Forms on Γ_H(N) separate points of one Γ₀(N)-orbit
-- statement:
--   Fix a natural number $N$ with $N \neq 0$ and a subgroup $H \leq (\mathbb{Z}/N)^{\times}$, and write $\Gamma_H(N)$ for the subgroup [`CohCarrier.GammaH N H`](def/CohCarrier_Level.html#L133) of $\mathrm{SL}_2(\mathbb{Z})$, namely the image in $\mathrm{SL}_2(\mathbb{Z})$ of those $\gamma \in \Gamma_0(N)$ whose associated unit of $\mathbb{Z}/N$ — the class of the lower right entry $\gamma_{1,1}$, invertible with inverse the class of $\gamma_{0,0}$ — lies in $H$. Let $\tau, \tau'$ be points of the upper half-plane such that $\gamma \cdot \tau \neq \tau'$ for every $\gamma \in \Gamma_H(N)$, and suppose there is some $\gamma_0 \in \mathrm{SL}_2(\mathbb{Z})$ lying in $\Gamma_0(N)$ with $\gamma_0 \cdot \tau = \tau'$. The conclusion asserts the existence of an integer weight $k$ and of two modular forms $g, h$ of weight $k$ for the image of $\Gamma_H(N)$ in $\mathrm{GL}_2(\mathbb{R})$ whose underlying functions on the upper half-plane satisfy $g(\tau)\,h(\tau') \neq g(\tau')\,h(\tau)$.
--
--   This is the residual, "diamond", case of the statement that modular forms on $\Gamma_H(N)$ separate $\Gamma_H(N)$-inequivalent points: here the two points lie in a single $\Gamma_0(N)$-orbit but in distinct $\Gamma_H(N)$-orbits, so they cannot be separated by forms pulled back from level $\Gamma_0(N)$. It is cited by [`ModularForm.exists_gammaH_apply_mul_apply_ne_of_forall_smul_ne`](thm.html#ModularForm.exists_gammaH_apply_mul_apply_ne_of_forall_smul_ne), which combines it with the $\Gamma_0(N)$-inequivalent case to obtain orbit separation in general.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularForm_exists_gammaH_apply_mul_apply_ne_of_forall_smul_ne_of_gamma0_smul_eq.lean

import Mathlib
import Definitions.Def_CohCarrier_Level

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups

theorem ModularForm.exists_gammaH_apply_mul_apply_ne_of_forall_smul_ne_of_gamma0_smul_eq (N : ℕ) [NeZero N]
    (H : Subgroup (ZMod N)ˣ) (τ τ' : UpperHalfPlane)
    (hτ : ∀ γ ∈ CohCarrier.GammaH N H, γ • τ ≠ τ')
    (γ₀ : SL(2, ℤ)) (hγ₀ : γ₀ ∈ CongruenceSubgroup.Gamma0 N) (hτ' : γ₀ • τ = τ') :
    ∃ (k : ℤ) (g h : ModularForm (CohCarrier.GammaH N H : Subgroup (GL (Fin 2) ℝ)) k),
      (g : UpperHalfPlane → ℂ) τ * (h : UpperHalfPlane → ℂ) τ' ≠
        (g : UpperHalfPlane → ℂ) τ' * (h : UpperHalfPlane → ℂ) τ := by sorry
