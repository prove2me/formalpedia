-- Prove2me | Theorems.Thm_ModularCurve_relfinrank_qExpFunctionFieldC_gammaH_gammaH_inf_gamma0_mul_eq_of_dvd
-- name    : ModularCurve.relfinrank_qExpFunctionFieldC_gammaH_gammaH_inf_gamma0_mul_eq_of_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:54.618386+00:00
-- url     : https://prove2.me/theorems/44907e9a-1e21-5aa1-859d-bf970528483b
-- title:
--   Degree ℓ for Γ_{H'}(N)∩Γ₀(Nℓ) when ℓ∣ N
-- statement:
--   Let $K$ be an algebraically closed field, $N$ a nonzero natural number, $H'$ a subgroup of $(\mathbf{Z}/N)^{\times}$, and $\ell$ a prime; assume $\ell \mid N$ and that the images of $N$ and of $\ell$ in $K$ are nonzero. Here [`CohCarrier.GammaH N H'`](def/CohCarrier_Level.html#L133) is the subgroup of $\mathrm{SL}_2(\mathbf{Z})$ consisting of those elements of $\Gamma_0(N)$ whose lower-right entry, reduced mod $N$ and regarded as a unit of $\mathbf{Z}/N$ via `gamma0Units`, lies in $H'$, and for a subgroup $\Gamma \le \mathrm{SL}_2(\mathbf{Z})$ the field [`ModularCurve.qExpFunctionFieldC K Γ`](def/ModularCurve_X1.html#L101) is the intermediate field of the Laurent series field $K((q))$ generated over $K$ by all quotients $\mathrm{intSeriesC}\,K\,p_f / \mathrm{intSeriesC}\,K\,p_g$, where $f,g$ are modular forms of a common weight $k$ for the image of $\Gamma$ in $\mathrm{GL}_2(\mathbf{R})$ with integral $q$-expansions $p_f,p_g \in \mathbf{Z}[[q]]$ and the denominator's image in $K((q))$ is nonzero. With the positivity instance for $N\ell$ supplied, the assertion is that the relative degree, in the sense of `IntermediateField.relfinrank`, of [`ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH N H' ⊓ CongruenceSubgroup.Gamma0 (N * ℓ))`](def/ModularCurve_X1.html#L101) over [`ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH N H')`](def/ModularCurve_X1.html#L101) — the degree of the former over the intersection of the two, the latter being contained in the former — equals $\ell$.
--
--   This is the function-field form of the classical index computation $[\Gamma_0(N):\Gamma_0(N\ell)] = \ell$ for a prime $\ell$ dividing $N$, transported to the $q$-expansion fields of $\Gamma_{H'}(N)$ and $\Gamma_{H'}(N)\cap\Gamma_0(N\ell)$ over an algebraically closed coefficient field of residue characteristic prime to $N$; it is the companion of the case $\ell \nmid N$, where the degree is $\ell+1$. It feeds the computations of degrees and relative degrees used in [`ModularCurve.finrankAlong_heckeAlphaModLH_eq_and_relfinrank_eq_of_charP_of_dvd_div`](thm.html#ModularCurve.finrankAlong_heckeAlphaModLH_eq_and_relfinrank_eq_of_charP_of_dvd_div) and [`ModularCurve.reducedRootFunction_genOpH_T_eq_smul_pow_mul_norm_heckeBetaModLH_of_abelJacobiPin_tauFree_of_algEquiv`](thm.html#ModularCurve.reducedRootFunction_genOpH_T_eq_smul_pow_mul_norm_heckeBetaModLH_of_abelJacobiPin_tauFree_of_algEquiv).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_relfinrank_qExpFunctionFieldC_gammaH_gammaH_inf_gamma0_mul_eq_of_dvd.lean

import Mathlib
import Definitions.Def_ModularCurve_XHDifferentialsModL

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ModularCurve.relfinrank_qExpFunctionFieldC_gammaH_gammaH_inf_gamma0_mul_eq_of_dvd
    (K : Type*) [Field K] [IsAlgClosed K] (N : ℕ) [NeZero N] (H' : Subgroup (ZMod N)ˣ)
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓN : ℓ ∣ N) (hNK : ((N : ℕ) : K) ≠ 0) (hℓK : ((ℓ : ℕ) : K) ≠ 0) :
    haveI : NeZero (N * ℓ) := ⟨Nat.mul_ne_zero (NeZero.ne N) (NeZero.ne ℓ)⟩
    IntermediateField.relfinrank (ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH N H'))
        (ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH N H' ⊓ CongruenceSubgroup.Gamma0 (N * ℓ))) = ℓ := by sorry
