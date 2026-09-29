-- Prove2me | Theorems.Thm_ModularCurve_relfinrank_qExpFunctionFieldC_gammaH_gammaH_inf_gamma0_mul_eq_add_one
-- name    : ModularCurve.relfinrank_qExpFunctionFieldC_gammaH_gammaH_inf_gamma0_mul_eq_add_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:54.618386+00:00
-- url     : https://prove2.me/theorems/0074e2c5-aac8-56cf-9cec-af910439eef9
-- title:
--   Degree ℓ+1 of the first degeneracy inclusion of q-expansion fields
-- statement:
--   Let $K$ be an algebraically closed field, $N\ge 1$ an integer, $H'\le(\mathbb{Z}/N)^\times$ a subgroup and $\ell$ a prime with $\gcd(\ell,N)=1$, and assume that the images of $N$ and of $\ell$ in $K$ are nonzero. For a subgroup $\Gamma\le \mathrm{SL}_2(\mathbb{Z})$ write $\bar F(\Gamma)=$ [`ModularCurve.qExpFunctionFieldC K Γ`](def/ModularCurve_X1.html#L101) for the intermediate field of the Laurent series field $K((q))$ generated over $K$ by the set `intFormRatiosC K Γ`, namely by all quotients $\mathrm{intSeriesC}_K(p_f)/\mathrm{intSeriesC}_K(p_g)$ where $f,g$ are modular forms of a common weight $k$ for the image of $\Gamma$ in $\mathrm{GL}_2(\mathbb{R})$, $p_f,p_g\in\mathbb{Z}[[q]]$ are integral $q$-expansions of $f$ and $g$ respectively, and the coefficientwise image $\mathrm{intSeriesC}_K(p_g)$ is nonzero. Here $\Gamma_{H'}(N)$ is the subgroup [`CohCarrier.GammaH N H'`](def/CohCarrier_Level.html#L133) of $\mathrm{SL}_2(\mathbb{Z})$ consisting of those $\gamma\in\Gamma_0(N)$ whose lower right entry reduces to an element of $H'$ in $(\mathbb{Z}/N)^\times$. The assertion is that the relative degree, in Mathlib's sense $[\,\bar F(\Gamma_{H'}(N)\cap\Gamma_0(N\ell)) : \bar F(\Gamma_{H'}(N))\cap \bar F(\Gamma_{H'}(N)\cap\Gamma_0(N\ell))\,]$, of these two subfields of $K((q))$ equals $\ell+1$.
--
--   This is the degree of the first of the two degeneracy inclusions of $q$-expansion function fields attached to the Hecke correspondence at $\ell$, the field-theoretic form of the statement that the degeneracy map $X_{H''}(N\ell)\to X_{H'}(N)$ has degree $\psi(N\ell)/\psi(N)=\ell+1$. It feeds the computation of Hecke operators at $\ell$ on the relevant function fields and the companion upper-bound-and-positivity statement for the same relative degree.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_relfinrank_qExpFunctionFieldC_gammaH_gammaH_inf_gamma0_mul_eq_add_one.lean

import Mathlib
import Definitions.Def_ModularCurve_XHDifferentialsModL

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ModularCurve.relfinrank_qExpFunctionFieldC_gammaH_gammaH_inf_gamma0_mul_eq_add_one
    (K : Type*) [Field K] [IsAlgClosed K] (N : ℕ) [NeZero N] (H' : Subgroup (ZMod N)ˣ)
    (ℓ : ℕ) [Fact ℓ.Prime] (hcop : ℓ.Coprime N) (hNK : ((N : ℕ) : K) ≠ 0) (hℓK : ((ℓ : ℕ) : K) ≠ 0) :
    haveI : NeZero (N * ℓ) := ⟨Nat.mul_ne_zero (NeZero.ne N) (NeZero.ne ℓ)⟩
    IntermediateField.relfinrank (ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH N H'))
        (ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH N H' ⊓ CongruenceSubgroup.Gamma0 (N * ℓ))) = ℓ + 1 := by sorry
