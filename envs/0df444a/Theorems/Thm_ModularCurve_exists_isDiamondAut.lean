-- Prove2me | Theorems.Thm_ModularCurve_exists_isDiamondAut
-- name    : ModularCurve.exists_isDiamondAut
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.903374+00:00
-- url     : https://prove2.me/theorems/edfc5e22-7fa8-5c31-a2b1-9644ed763d63
-- title:
--   Existence of diamond automorphisms of F(Γ₁(M))
-- statement:
--   Let $M$ be a nonzero natural number and let $d$ be a natural number with $\gcd(d,M)=1$. Write $F =$ [`ModularCurve.x1FunctionField M`](def/ModularCurve_X1.html#L137), the intermediate field `qExpFunctionFieldC ℚ (Gamma1 M)` of the Laurent series field $\mathbb{Q}((q))$ attached to $\Gamma_1(M)$. The assertion is that there exists a $\mathbb{Q}$-algebra automorphism $\sigma$ of $F$ satisfying [`ModularCurve.IsDiamondAut M d σ`](def/ModularCurve_X1Diamond.html#L53), that is: $d$ is coprime to $M$, and for every weight $k \in \mathbb{Z}$, all modular forms $f,g$ of weight $k$ on the image of $\Gamma_1(M)$ in $\mathrm{GL}_2(\mathbb{R})$, all integral power series $p_f,p_g \in \mathbb{Z}[[q]]$ whose images in $\mathbb{C}[[q]]$ are the $q$-expansions of $f$ and $g$ (period $1$), with the Laurent series attached to $p_g$ over $\mathbb{Q}$ nonzero, and every $\gamma \in \mathrm{SL}_2(\mathbb{Z})$ lying in $\Gamma_0(M)$ with $\gamma_{00} \equiv d \pmod M$, the element $\sigma$ applied to the quotient of the Laurent series of $p_f$ by that of $p_g$, mapped coefficientwise into $\mathbb{C}((q))$, multiplied by the $q$-expansion of $g \mid_k \gamma$, equals the $q$-expansion of $f \mid_k \gamma$. The proof cites [`ModularCurve.exists_isIntegralQExp_smul_slash_of_mem_Gamma0`](thm.html#ModularCurve.exists_isIntegralQExp_smul_slash_of_mem_Gamma0).
--
--   This produces the diamond operator $\langle d\rangle$ for $d$ prime to $M$ as an automorphism of the $q$-expansion function field of $X_1(M)$ over $\mathbb{Q}$, characterised by its effect on ratios of Fourier expansions of forms of equal weight. It is used in the study of the $\mathbb{Q}$-model of $X_1(M)$, in particular in results relating diamond automorphisms to Atkin–Lehner and Hecke operators and to the associated valuation subrings.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_isDiamondAut.lean

import Mathlib
import Definitions.Def_ModularCurve_X1Diamond

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ModularCurve.exists_isDiamondAut (M : ℕ) [NeZero M] {d : ℕ} (hd : Nat.Coprime d M) :
    ∃ σ : ModularCurve.x1FunctionField M ≃ₐ[ℚ] ModularCurve.x1FunctionField M,
      ModularCurve.IsDiamondAut M d σ := by sorry
