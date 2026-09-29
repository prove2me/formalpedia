-- Prove2me | Theorems.Thm_ModularCurve_qExpand_jqModC_mem_qExpFunctionFieldC_gammaH_inf_gamma0_mul
-- name    : ModularCurve.qExpand_jqModC_mem_qExpFunctionFieldC_gammaH_inf_gamma0_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.985053+00:00
-- url     : https://prove2.me/theorems/c3926d57-5945-54d2-bf7c-d101c0a852dc
-- title:
--   j(q^ℓ) in the q-expansion field of Γ_H(N)∩Γ₀(Nℓ)
-- statement:
--   Let $K$ be a field, $N \ge 1$, $\ell$ a prime, and let $H$ be a subgroup of $(\mathbb{Z}/N)^\times$; assume $N\ell \neq 0$ in $K$ and $\ell \nmid N$. Let [`ModularCurve.jqModC K`](def/ModularCurve_JqCoeff.html#L15) be the Laurent series $q^{-1}\cdot \overline{E_4^3\,\eta^{-24}}$ over $K$, i.e. the monomial $q^{-1}$ times the image in $K[[q]]$ of the integral power series `jNum` $= E_4^3 \cdot$ `dedekindEtaUnitInv`, and let [`ModularCurve.qExpand K ℓ`](def/ModularCurve_X0.html#L25) be the ring endomorphism of $K((q))$ obtained by multiplying all exponents by $\ell$, that is $q \mapsto q^{\ell}$. For a subgroup $\Gamma \le \mathrm{SL}_2(\mathbb{Z})$, `qExpFunctionFieldC K Γ` denotes the intermediate field of $K((q))$ generated over $K$ by the set of quotients $\mathrm{intSeriesC}\,K\,p_f / \mathrm{intSeriesC}\,K\,p_g$, where $f,g$ are modular forms of one and the same weight $k$ on the image of $\Gamma$ in $\mathrm{GL}_2(\mathbb{R})$, $p_f, p_g$ are integral power series that are $q$-expansions of $f$ and $g$, and the reduction of $p_g$ to $K$ is nonzero. The conclusion is that $j(q^{\ell})$ lies in this field for the group [`CohCarrier.GammaH N H`](def/CohCarrier_Level.html#L133) $\cap\ \Gamma_0(N\ell)$, where `GammaH N H` consists of the matrices of $\Gamma_0(N)$ whose lower right entry reduces modulo $N$ into $H$. The proof uses neither the hypothesis $N\ell \neq 0$ in $K$ nor the hypothesis $\ell \nmid N$.
--
--   This is the inclusion, in $q$-expansion form, expressing that $j(q^\ell)$ is a modular function on $\Gamma_H(N) \cap \Gamma_0(N\ell)$, the classical source of the modular equation relating $j(q)$ and $j(q^\ell)$. It feeds the identification of the $q$-expansion function field of $\Gamma_H(N) \cap \Gamma_0(N\ell)$ as the field of $\Gamma_H(N)$ adjoined with $j(q^\ell)$, and thence the cuspidality criterion for specialisations of places on these curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_qExpand_jqModC_mem_qExpFunctionFieldC_gammaH_inf_gamma0_mul.lean

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_CohCarrier_Level

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups

theorem ModularCurve.qExpand_jqModC_mem_qExpFunctionFieldC_gammaH_inf_gamma0_mul
    (K : Type*) [Field K] (N : ℕ) [NeZero N] (ℓ : ℕ) [Fact ℓ.Prime]
    (hNℓ : ((N * ℓ : ℕ) : K) ≠ 0) (hℓN : ¬ ℓ ∣ N) (H : Subgroup (ZMod N)ˣ) :
    ModularCurve.qExpand K ℓ (ModularCurve.jqModC K) ∈ ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH N H ⊓ CongruenceSubgroup.Gamma0 (N * ℓ)) := by sorry
