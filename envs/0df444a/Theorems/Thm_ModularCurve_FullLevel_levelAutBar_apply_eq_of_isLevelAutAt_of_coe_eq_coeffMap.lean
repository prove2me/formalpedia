-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_levelAutBar_apply_eq_of_isLevelAutAt_of_coe_eq_coeffMap
-- name    : ModularCurve.FullLevel.levelAutBar_apply_eq_of_isLevelAutAt_of_coe_eq_coeffMap
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:38.446507+00:00
-- url     : https://prove2.me/theorems/63ddfedf-4f81-5360-9220-0e867a0c5f39
-- title:
--   Level automorphism over L agrees coefficientwise with `levelAutBar`
-- statement:
--   Let $q\ge 5$ be a prime, $M'$ a nonzero natural number with $q\nmid M'$, and let $L$ be a field of characteristic zero containing a primitive $q$-th root of unity $\zeta$, such that some ring homomorphism $L\to\mathbb{C}$ carries $\zeta$ to $e^{2\pi i/q}$. Let $K$ be the intermediate field $L\subseteq K\subseteq L((X))$ obtained as `laurentBaseChange`, i.e. generated over $L$ by the coefficientwise image of the function field `xHFunctionField` of level $q^2M'$ with $H=\ker\bigl((\mathbb{Z}/q^2M')^\times\to(\mathbb{Z}/q)^\times\bigr)$. Let $e:L\to\overline{\mathbb{Q}}$ be a ring homomorphism, $\zeta'$ a primitive $q$-th root of unity in $\overline{\mathbb{Q}}$ with $\zeta'=e(\zeta)$, and $\iota_K:K\to$ `fieldBar`$\,q\,M'$ a ring homomorphism acting on Laurent series by applying $e$ to each coefficient. Let $\varepsilon\in SL_2(\mathbb{Z})$ lie in $\Gamma_0(M')$ and let $\sigma$ be an $L$-algebra automorphism of $K$ satisfying `IsLevelAutAt` for the data $(L,q,\zeta,q,q^2M',H,\varepsilon)$: for every weight $k$, all modular forms $f,g$ on $\Gamma_H(q^2M')$ of weight $k$ with integral $q$-expansions $p_f,p_g$, $p_g$ having nonzero constant-series image, every $x\in K$ whose Laurent series is the image of $p_f/p_g$, and every $\iota:L\to\mathbb{C}$ sending $\zeta$ to $e^{2\pi i/q}$, one has $\iota(\sigma x)\cdot q\text{-exp}(g\mid_k \gamma_q(\varepsilon))=q\text{-exp}(f\mid_k \gamma_q(\varepsilon))$, where $\gamma_q(\varepsilon)=\begin{pmatrix}a&b/q\\ qc&d\end{pmatrix}$. Then for each $x\in K$, $\iota_K(\sigma x)=$ `levelAutBar`$\,q\,M'\,\zeta'\,\varepsilon\,(\iota_K x)$, the latter being the automorphism of `fieldBar` chosen to satisfy the corresponding condition `IsLevelAutBar` over $\overline{\mathbb{Q}}$ (and the identity if none exists).
--
--   This is the comparison statement identifying the canonically chosen geometric level automorphism of the function field of the $\Gamma_H$-curve over $\overline{\mathbb{Q}}$ with any automorphism satisfying the same $q$-expansion characterisation over a field $L$ of constants mapping into $\overline{\mathbb{Q}}$, the identification being coefficientwise on Laurent series. It is used in the analysis of the Gauss valuation and of the stabiliser of the line at infinity, and in the computation of the action of level automorphisms on $q$-expansions.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_levelAutBar_apply_eq_of_isLevelAutAt_of_coe_eq_coeffMap.lean

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_XH
import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_ModularCurve_FullLevelLevelAutAt

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups

theorem ModularCurve.FullLevel.levelAutBar_apply_eq_of_isLevelAutAt_of_coe_eq_coeffMap
    (q : ℕ) [Fact q.Prime] (hq : 5 ≤ q) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (L : Type) [Field L] [CharZero L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ q)
    (hι : ∃ ι : L →+* ℂ, ι ζ = Complex.exp (2 * Real.pi * Complex.I / q))
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L
      (ModularCurve.xHFunctionField (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M')))
    (e : L →+* AlgebraicClosure ℚ)
    (ζ' : ModularCurve.FullLevel.Idx q) (hζ' : ζ'.val = e ζ)
    (ιK : ↥K →+* ↥(ModularCurve.FullLevel.fieldBar q M'))
    (hιK : ∀ x : ↥K, ((ιK x : ↥(ModularCurve.FullLevel.fieldBar q M')) : LaurentSeries (AlgebraicClosure ℚ)) =
      ModularCurve.coeffMap e (x : LaurentSeries L))
    (ε : SL(2, ℤ)) (hε : ε ∈ CongruenceSubgroup.Gamma0 M')
    (σ : ↥K ≃ₐ[L] ↥K)
    (hσ : ModularCurve.FullLevel.IsLevelAutAt L q ζ q (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M') ε K σ)
    (x : ↥K) :
    ιK (σ x) = ModularCurve.FullLevel.levelAutBar q M' ζ' ε (ιK x) := by sorry
