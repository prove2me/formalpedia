-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_Diamond_levelAut_apply_qExpand_jq_eq_jqNModC_of_antidiagonal_of_ringHom_of_eq_levelH_inf_ker
-- name    : ModularCurve.FullLevel.Diamond.levelAut_apply_qExpand_jq_eq_jqNModC_of_antidiagonal_of_ringHom_of_eq_levelH_inf_ker
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:30.533368+00:00
-- url     : https://prove2.me/theorems/f4d2b1af-e40b-5f14-b73a-6825ea72ae0a
-- title:
--   Level automorphism sends j(qᵈ) to j(q^q²d)
-- statement:
--   Let $q$ be a prime and $M'\ge 1$ a natural number with $q\nmid M'$, and let $\ell_g$ be a prime with $\ell_g\equiv 11\pmod{12}$ and $\ell_g\mid M'$. Let $L$ be a field of characteristic zero, $\xi\in L$ a primitive $(q\ell_g)$-th root of unity such that some ring homomorphism $\iota:L\to\mathbb C$ satisfies $\iota(\xi)=e^{2\pi i/(q\ell_g)}$, and let $e:L\to\overline{\mathbb Q}$ be a ring homomorphism. Let $H_1\le(\mathbb Z/q^2M')^\times$ be the intersection of [`ModularCurve.FullLevel.levelH q M'`](def/ModularCurve_FullLevelJacobian.html#L22), the kernel of reduction $(\mathbb Z/q^2M')^\times\to(\mathbb Z/q)^\times$, with the kernel of reduction to $(\mathbb Z/\ell_g)^\times$, i.e. the units congruent to $1$ modulo $q$ and modulo $\ell_g$. Let $K\subseteq L(\!(\mathfrak q)\!)$ be the intermediate field obtained by adjoining to $L$ the image under coefficientwise extension of scalars of the rational $\mathfrak q$-expansion function field [`ModularCurve.xHFunctionField (q ^ 2 * M') H₁`](def/ModularCurve_XH.html#L79) attached to the subgroup $\Gamma_{H_1}(q^2M')\le\mathrm{SL}_2(\mathbb Z)$ (the image in $\Gamma_0(q^2M')$ of the preimage of $H_1$ under the diagonal-unit character). Let $\gamma\in\mathrm{SL}_2(\mathbb Z)$ lie in $\Gamma_0(M')\cap\Gamma_1(\ell_g)$ with $\gamma_{00}\equiv\gamma_{11}\equiv 0\pmod q$, and let $\tau$ be an $L$-algebra automorphism of $K$ satisfying [`ModularCurve.FullLevel.IsLevelAutAt`](def/ModularCurve_FullLevelLevelAutAt.html#L29) for the data $(L,q,\xi^{\ell_g},q,q^2M',H_1,\gamma^{-1})$: for every weight $k\in\mathbb Z$, all modular forms $f,g$ of weight $k$ on the subgroup of $\mathrm{GL}_2(\mathbb R)$ attached to $\Gamma_{H_1}(q^2M')$, all integral power series $p_f,p_g$ whose complex reductions are the $\mathfrak q$-expansions of $f$ and $g$ with the Laurent series of $p_g$ over $\mathbb Q$ nonzero, every $x\in K$ whose underlying Laurent series is the image of that ratio of expansions, and every ring homomorphism $\iota:L\to\mathbb C$ with $\iota(\xi^{\ell_g})=e^{2\pi i/q}$, the coefficientwise image under $\iota$ of $\tau x$ times the $\mathfrak q$-expansion of $g\mid_k\,$`conjElemN q γ⁻¹` equals the $\mathfrak q$-expansion of $f\mid_k\,$`conjElemN q γ⁻¹`, where `conjElemN m γ` is the matrix $\bigl(\begin{smallmatrix}\gamma_{00}&\gamma_{01}/m\\ m\gamma_{10}&\gamma_{11}\end{smallmatrix}\bigr)$. Finally let $d\ge 1$ divide $M'$ and assume that the series $j(\mathfrak q^{d})$ (the image in $L(\!(\mathfrak q)\!)$ of [`ModularCurve.qExpand ℚ d ModularCurve.jq`](def/ModularCurve_X0.html#L25)), $j(\mathfrak q^{q^2 d})$ and $j(\mathfrak q^{q d})$ (the series [`ModularCurve.jqNModC L`](def/ModularCurve_JqCoeff.html#L18) at $q\cdot q\cdot d$ and $q\cdot d$) all lie in $K$. Then $\tau$ carries the element $j(\mathfrak q^{d})$ of $K$ to $j(\mathfrak q^{q^{2}d})$ and fixes $j(\mathfrak q^{qd})$.
--
--   This records how the level automorphism attached to an anti-diagonal-mod-$q$ element $\gamma\in\Gamma_0(M')\cap\Gamma_1(\ell_g)$ acts on the $j$-series at the divisors $d, qd, q^2d$ inside the function field of $X_{H_1}(q^2M')$ over $L$: it interchanges the two outer Tate-type expansions and fixes the middle one. It is used in the computation of the action on the cyclic quotient of the Jacobian at a Tate point, in [`ModularCurve.FullLevel.Diamond.apply_eq_cyclicQuotientJ_pow_of_levelAut_of_originChart_of_forall_nsmul_eq_zero_rigidDataH1Pow_of_tatePoint_pinGamma1`](thm.html#ModularCurve.FullLevel.Diamond.apply_eq_cyclicQuotientJ_pow_of_levelAut_of_originChart_of_forall_nsmul_eq_zero_rigidDataH1Pow_of_tatePoint_pinGamma1).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_Diamond_levelAut_apply_qExpand_jq_eq_jqNModC_of_antidiagonal_of_ringHom_of_eq_levelH_inf_ker.lean

import Mathlib
import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_ModularCurve_FullLevelLevelAutAt
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_XH

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups

theorem ModularCurve.FullLevel.Diamond.levelAut_apply_qExpand_jq_eq_jqNModC_of_antidiagonal_of_ringHom_of_eq_levelH_inf_ker
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (ℓg : ℕ) (hℓg : ℓg.Prime) (hℓg12 : ℓg % 12 = 11) (hℓgM' : ℓg ∣ M')
    (L : Type) [Field L] [CharZero L]
    (ξ : L) (hξ : IsPrimitiveRoot ξ (q * ℓg))
    (hι : ∃ ι : L →+* ℂ, ι ξ = Complex.exp (2 * Real.pi * Complex.I / (q * ℓg)))
    (e : L →+* AlgebraicClosure ℚ)
    (H₁ : Subgroup (ZMod (q ^ 2 * M'))ˣ)
    (hH₁ : H₁ = ModularCurve.FullLevel.levelH q M' ⊓ (ZMod.unitsMap (Dvd.dvd.mul_left hℓgM' (q ^ 2))).ker)
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L
      (ModularCurve.xHFunctionField (q ^ 2 * M') H₁))
    (γ : SL(2, ℤ)) (hγ0 : γ ∈ CongruenceSubgroup.Gamma0 M') (hγℓ : γ ∈ CongruenceSubgroup.Gamma1 ℓg)
    (hγq : ((γ 0 0 : ℤ) : ZMod q) = 0 ∧ ((γ 1 1 : ℤ) : ZMod q) = 0)
    (τ : ↥K ≃ₐ[L] ↥K)
    (hτ : ModularCurve.FullLevel.IsLevelAutAt L q (ξ ^ ℓg) q (q ^ 2 * M') H₁ γ⁻¹ K τ)
    (d : ℕ) [NeZero d] (hd : d ∣ M') [NeZero (q * d)] [NeZero (q * q * d)]
    (hbK : ModularCurve.coeffEmb L (ModularCurve.qExpand ℚ d ModularCurve.jq) ∈ K)
    (hbPK : ModularCurve.jqNModC L (q * q * d) ∈ K)
    (hcK : ModularCurve.jqNModC L (q * d) ∈ K) :
    τ ⟨_, hbK⟩ = ⟨_, hbPK⟩ ∧ τ ⟨_, hcK⟩ = ⟨_, hcK⟩ := by sorry
