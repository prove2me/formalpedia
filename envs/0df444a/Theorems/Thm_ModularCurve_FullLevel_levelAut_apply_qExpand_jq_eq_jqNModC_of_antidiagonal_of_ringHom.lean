-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_levelAut_apply_qExpand_jq_eq_jqNModC_of_antidiagonal_of_ringHom
-- name    : ModularCurve.FullLevel.levelAut_apply_qExpand_jq_eq_jqNModC_of_antidiagonal_of_ringHom
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:38.446507+00:00
-- url     : https://prove2.me/theorems/f21d1940-3681-518b-9873-cf63a463bb33
-- title:
--   Anti-diagonal level automorphism shifts the j-readings
-- statement:
--   Let $q\ge 5$ be a prime, $M'$ a nonzero natural number with $q\nmid M'$, and $\ell'\ge 3$ a prime with $\ell'\ne q$ and $\ell'\nmid M'$. Let $L$ be a field of characteristic $0$, $\xi\in L$ a primitive $(q\ell')$-th root of unity such that some ring homomorphism $L\to\mathbb C$ carries $\xi$ to $\exp(2\pi i/(q\ell'))$, and let $e:L\to\overline{\mathbb Q}$ be a ring homomorphism. Let $K$ be the intermediate field of $L\subseteq \mathrm{LaurentSeries}\,L$ obtained by adjoining to $L$ the coefficientwise image under $\mathbb Q\to L$ of the $q$-expansion function field `xHFunctionField` of level $(q\ell')^2M'$ and group `levelH` $(q\ell')\,M'$, the latter being the kernel of the reduction $(\mathbb Z/(q\ell')^2M')^\times\to(\mathbb Z/q\ell')^\times$. Let $\gamma\in SL_2(\mathbb Z)$ lie in $\Gamma_0(M')\cap\Gamma(\ell')$ and satisfy $\gamma_{00}\equiv\gamma_{11}\equiv 0 \pmod q$, and let $\tau$ be an $L$-algebra automorphism of $K$ which is a level automorphism at $\gamma^{-1}$ in the sense of `IsLevelAutAt` for the data $(q\ell',\xi,q\ell',(q\ell')^2M',$ `levelH` $(q\ell')M')$: for all weights $k$ and all weight-$k$ modular forms $f,g$ for $\Gamma_H((q\ell')^2M')$ with integral $q$-expansions $p_f,p_g$, $p_g\ne 0$ in $\mathrm{LaurentSeries}\,\mathbb Q$, and every $x\in K$ whose Laurent series is the image of $p_f/p_g$, the complex reading of $\tau x$ along any $\iota:L\to\mathbb C$ with $\iota\xi=\exp(2\pi i/(q\ell'))$ multiplies the $q$-expansion of $g\mid_k \mathrm{conjElemN}\,(q\ell')\,\gamma^{-1}$ into that of $f\mid_k \mathrm{conjElemN}\,(q\ell')\,\gamma^{-1}$, where $\mathrm{conjElemN}\,m\,\delta=\begin{pmatrix}\delta_{00}&\delta_{01}/m\\ m\delta_{10}&\delta_{11}\end{pmatrix}$. Finally let $d$ be a nonzero divisor of $M'$, and assume that the three Laurent series $\mathrm{qExpand}_L\,\ell'$ applied to the coefficientwise image of $\mathrm{qExpand}_{\mathbb Q}\,d$ of the $j$-series $jq$, and the $j$-series $\mathrm{jqNModC}_L$ at $q^2\ell'd$ and at $q\ell'd$, all lie in $K$. Then $\tau$ carries the first of these elements to $\mathrm{jqNModC}_L(q^2\ell'd)$ and fixes $\mathrm{jqNModC}_L(q\ell'd)$.
--
--   In the classical language, with local parameter $\mathfrak q=e^{2\pi i z/(q\ell')}$ the three elements are the readings $j((d/q)z)$, $j(qdz)$ and $j(dz)$: the level automorphism attached to an element of $\Gamma_0(M')\cap\Gamma(\ell')$ that is anti-diagonal modulo $q$ interchanges the two $j$-readings lying above the cyclic $q$-isogeny, while the reading $j(dz)$, being $\Gamma_0(d)$-invariant, is fixed. It is used in the identification of the values of these readings at the Tate point in terms of the cyclic quotient $j$-invariant.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_levelAut_apply_qExpand_jq_eq_jqNModC_of_antidiagonal_of_ringHom.lean

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

theorem ModularCurve.FullLevel.levelAut_apply_qExpand_jq_eq_jqNModC_of_antidiagonal_of_ringHom
    (q : ℕ) [Fact q.Prime] (hq : 5 ≤ q) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (ℓ' : ℕ) [Fact ℓ'.Prime] (hℓ'3 : 3 ≤ ℓ') (hℓ'q : ℓ' ≠ q) (hℓ'M' : ¬ ℓ' ∣ M')
    (L : Type) [Field L] [CharZero L]
    (ξ : L) (hξ : IsPrimitiveRoot ξ (q * ℓ'))
    (hι : ∃ ι : L →+* ℂ, ι ξ = Complex.exp (2 * Real.pi * Complex.I / (q * ℓ')))
    (e : L →+* AlgebraicClosure ℚ)
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L
      (ModularCurve.xHFunctionField ((q * ℓ') ^ 2 * M') (ModularCurve.FullLevel.levelH (q * ℓ') M')))
    (γ : SL(2, ℤ)) (hγ0 : γ ∈ CongruenceSubgroup.Gamma0 M') (hγℓ : γ ∈ CongruenceSubgroup.Gamma ℓ')
    (hγq : ((γ 0 0 : ℤ) : ZMod q) = 0 ∧ ((γ 1 1 : ℤ) : ZMod q) = 0)
    (τ : ↥K ≃ₐ[L] ↥K)
    (hτ : ModularCurve.FullLevel.IsLevelAutAt L (q * ℓ') ξ (q * ℓ') ((q * ℓ') ^ 2 * M')
      (ModularCurve.FullLevel.levelH (q * ℓ') M') γ⁻¹ K τ)
    (d : ℕ) [NeZero d] (hd : d ∣ M') [NeZero (q * ℓ' * d)] [NeZero (q * q * ℓ' * d)]
    (hbK : ModularCurve.qExpand L ℓ' (ModularCurve.coeffEmb L (ModularCurve.qExpand ℚ d ModularCurve.jq)) ∈ K)
    (hbPK : ModularCurve.jqNModC L (q * q * ℓ' * d) ∈ K)
    (hcK : ModularCurve.jqNModC L (q * ℓ' * d) ∈ K) :
    τ ⟨_, hbK⟩ = ⟨_, hbPK⟩ ∧ τ ⟨_, hcK⟩ = ⟨_, hcK⟩ := by sorry
