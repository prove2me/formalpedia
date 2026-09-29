-- Prove2me | Theorems.Thm_ModularCurve_qExpFrobeniusModL_eq_inv_qExpArithFrobC_smul_pow
-- name    : ModularCurve.qExpFrobeniusModL_eq_inv_qExpArithFrobC_smul_pow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.985053+00:00
-- url     : https://prove2.me/theorems/f369719e-7936-59b5-aa0a-0e7fc6a83f61
-- title:
--   Geometric Frobenius as p-th power of the inverse arithmetic Frobenius
-- statement:
--   Let $p$ be a prime and let $K$ be a perfect field of characteristic $p$, and let $\Gamma$ be a subgroup of $\mathrm{SL}_2(\mathbb{Z})$. Write $F(\Gamma) =$ [`ModularCurve.qExpFunctionFieldC K Γ`](def/ModularCurve_X1.html#L101) for the intermediate field of the Laurent series field $K(\!(q)\!)$ obtained by adjoining to $K$ all quotients $\iota(p_f)/\iota(p_g)$, where $f,g$ are modular forms of a common weight for the image of $\Gamma$ in $\mathrm{GL}_2(\mathbb{R})$ whose $q$-expansions are given by integral power series $p_f,p_g$, the series $\iota(p_g)$ obtained from $p_g$ over $K$ being nonzero. Two operators on $F(\Gamma)$ are involved: [`ModularCurve.qExpFrobeniusModL K Γ p`](def/ModularCurve_QExpFrobeniusModL.html#L76), the $K$-algebra endomorphism of $F(\Gamma)$ induced by the substitution $q \mapsto q^p$ on $K(\!(q)\!)$ (multiplication by $p$ on exponents of the Hahn series), and [`ModularCurve.qExpArithFrobC p K Γ`](def/ModularCurve_QExpCoeffSemilinearAut.html#L188), the element of the group of semilinear automorphisms $\{(\sigma,\tau) \in \mathrm{Aut}(F(\Gamma)) \times \mathrm{Aut}(K) : \sigma \circ \mathrm{alg} = \mathrm{alg} \circ \tau\}$ whose second component is the Frobenius $a \mapsto a^p$ of $K$ and whose first component is the induced coefficientwise Frobenius on $F(\Gamma)$. The assertion is that for every $f \in F(\Gamma)$,
--   $$\mathrm{qExpFrobeniusModL}(f) = \bigl(\mathrm{qExpArithFrobC}^{-1} \cdot f\bigr)^{p},$$
--   the inverse acting by extraction of $p$-th roots of coefficients, which is available since $K$ is perfect.
--
--   This is the factorisation of the absolute Frobenius of the function field $F(\Gamma)$ in characteristic $p$ into its arithmetic part (coefficientwise Frobenius of $K$) and its geometric part ($q \mapsto q^p$): the geometric Frobenius is the $p$-th power map twisted by the inverse of the arithmetic Frobenius. It is used in the analysis of the reduction of the modular curve and its places at $p$, in particular to identify the place obtained by restriction along the geometric Frobenius with a translate of a given place under the arithmetic Frobenius.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_qExpFrobeniusModL_eq_inv_qExpArithFrobC_smul_pow.lean

import Mathlib
import Definitions.Def_ModularCurve_QExpFrobeniusModL
import Definitions.Def_ModularCurve_QExpCoeffSemilinearAut
import Definitions.Def_AlgebraicCurve_Correspondence

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve
open scoped MatrixGroups

theorem ModularCurve.qExpFrobeniusModL_eq_inv_qExpArithFrobC_smul_pow
    (p : ℕ) [Fact p.Prime] (K : Type*) [Field K] [CharP K p] [PerfectField K] (Γ : Subgroup SL(2, ℤ))
    (f : ModularCurve.qExpFunctionFieldC K Γ) :
    ModularCurve.qExpFrobeniusModL K Γ p f = ((ModularCurve.qExpArithFrobC p K Γ)⁻¹ • f) ^ p := by sorry
