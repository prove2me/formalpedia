-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_forall_isLevelAutAt_apply_eq_iff_exists_eq_qExpand
-- name    : ModularCurve.FullLevel.forall_isLevelAutAt_apply_eq_iff_exists_eq_qExpand
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:37.725148+00:00
-- url     : https://prove2.me/theorems/28d962b1-2c65-5ee5-86fc-af40645fb3c7
-- title:
--   Fixed field of the Γ₀(M') level automorphisms is qτ-expansions
-- statement:
--   Fix a prime $q$ with $q \ge 5$ and a nonzero natural number $M'$ with $q \nmid M'$, a field $L$ of characteristic zero, an element $\zeta \in L$ that is a primitive $q$-th root of unity, and assume there exists a ring homomorphism $\iota_0 : L \to \mathbb{C}$ with $\iota_0(\zeta) = e^{2\pi i/q}$. Let $H = \mathrm{levelH}\ q\ M'$ be the kernel of the reduction $(\mathbb{Z}/q^2M')^\times \to (\mathbb{Z}/q)^\times$, i.e. the units congruent to $1$ modulo $q$, and let $\Gamma_H(q^2M') \le \mathrm{SL}_2(\mathbb{Z})$ be the associated group. Let $K$ be the intermediate field of $L \subseteq \mathrm{LaurentSeries}\,L$ obtained by adjoining to $L$ the coefficientwise images under $\mathbb{Q} \to L$ of the elements of $\mathrm{xHFunctionField}(q^2M', H)$, the subfield of $\mathrm{LaurentSeries}\,\mathbb{Q}$ generated over $\mathbb{Q}$ by the quotients $p_f/p_g$ of $q$-expansions coming from pairs of modular forms $f, g$ of a common weight $k$ for $\Gamma_H(q^2M')$ having integral $q$-expansions $p_f, p_g$ with $p_g \ne 0$ in $\mathrm{LaurentSeries}\,\mathbb{Q}$. Let $\tau : \mathrm{SL}_2(\mathbb{Z}) \to (K \simeq_{\mathrm{alg}[L]} K)$ be any family of $L$-algebra automorphisms of $K$ such that for every $\gamma \in \Gamma_0(M')$ the automorphism $\tau(\gamma)$ satisfies $\mathrm{IsLevelAutAt}$ for $\gamma^{-1}$ at scaling parameter $q$: for all $k$, all weight-$k$ forms $f, g$ for $\Gamma_H(q^2M')$ with integral $q$-expansions $p_f, p_g$, $p_g \ne 0$, all $x \in K$ whose Laurent series is the image of $p_f/p_g$, and every ring homomorphism $\iota : L \to \mathbb{C}$ with $\iota(\zeta) = e^{2\pi i/q}$, one has $\iota(\tau(\gamma)x) \cdot (g \mid_k \gamma^{-1,\sharp}) = (f \mid_k \gamma^{-1,\sharp})$ as $q$-expansion series over $\mathbb{C}$, where $\delta^{\sharp} = \mathrm{diag}(q,1)^{-1}\delta\,\mathrm{diag}(q,1)$. Then for every $w \in K$: $\tau(\gamma)w = w$ for all $\gamma \in \Gamma_0(M')$ if and only if there is a Laurent series $x$ in the field obtained from $\mathrm{qExpFunctionFieldC}\ \mathbb{Q}\ \Gamma_0(M')$ by the same coefficientwise base change to $L$, such that the Laurent series underlying $w$ equals $\mathrm{qExpand}\ L\ q$ applied to $x$, i.e. the series obtained from $x$ by multiplying all exponents by $q$.
--
--   This is the Galois-descent step identifying the common fixed field of the level automorphisms attached to $\Gamma_0(M')$ acting on the $L$-rational function field of $X_H(q^2M')$ as the field of $\Gamma_0(M')$-functions in the variable $q\tau$, in the style of Shimura's description of fields of modular functions and their automorphisms. It is used downstream in the auxiliary-level version of the same statement and in the comparisons of Gauss-sum data and of the $j$-chart attached to these function fields.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_forall_isLevelAutAt_apply_eq_iff_exists_eq_qExpand.lean

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_ModularCurve_FullLevelLevelAutAt

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups

theorem ModularCurve.FullLevel.forall_isLevelAutAt_apply_eq_iff_exists_eq_qExpand
    (q : ℕ) [Fact q.Prime] (hq : 5 ≤ q) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (L : Type) [Field L] [CharZero L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ q)
    (hι : ∃ ι : L →+* ℂ, ι ζ = Complex.exp (2 * Real.pi * Complex.I / q))
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L
      (ModularCurve.xHFunctionField (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M')))

    (τ : SL(2, ℤ) → (↥K ≃ₐ[L] ↥K))
    (hτ : ∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 M' →
      ModularCurve.FullLevel.IsLevelAutAt L q ζ q (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M') γ⁻¹ K (τ γ))
    :
    ∀ w : ↥K,
      (∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 M' → τ γ w = w) ↔
        ∃ x : LaurentSeries L,
          x ∈ ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 M')) ∧
          ((w : ↥K) : LaurentSeries L) = ModularCurve.qExpand L q x := by sorry
