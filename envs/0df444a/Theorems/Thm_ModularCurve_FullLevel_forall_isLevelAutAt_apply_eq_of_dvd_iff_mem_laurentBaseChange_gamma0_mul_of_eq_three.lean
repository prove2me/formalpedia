-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_forall_isLevelAutAt_apply_eq_of_dvd_iff_mem_laurentBaseChange_gamma0_mul_of_eq_three
-- name    : ModularCurve.FullLevel.forall_isLevelAutAt_apply_eq_of_dvd_iff_mem_laurentBaseChange_gamma0_mul_of_eq_three
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:37.725148+00:00
-- url     : https://prove2.me/theorems/900f7754-04ac-5055-8cb5-239930c3ce94
-- title:
--   Fixed field of the Borel level automorphisms, q=3
-- statement:
--   Let $q$ be a prime with $q=3$, let $M'$ be a nonzero natural number with $q \nmid M'$, and let $L$ be a field of characteristic zero containing an element $\zeta$ that is a primitive $q$-th root of unity and admitting a ring homomorphism $\iota_0 : L \to \mathbb{C}$ with $\iota_0\zeta = e^{2\pi i/q}$. Let $K$ be the intermediate field of $L \subseteq \mathrm{LaurentSeries}\,L$ obtained as `laurentBaseChange`, that is, the subfield generated over $L$ by the coefficientwise images under $\mathbb{Q}\to L$ of `xHFunctionField` at level $q^2M'$ with group $H=$ `levelH` $q\,M'$, the kernel of the reduction $(\mathbb{Z}/q^2M')^\times \to (\mathbb{Z}/q)^\times$; that field is generated over $\mathbb{Q}$ by the ratios $P_f/P_g$ of Laurent series attached to integral $q$-expansions (of width $1$) of pairs of weight-$k$ modular forms $f,g$ on the subgroup of $\mathrm{GL}_2(\mathbb{R})$ determined by $\Gamma_H(q^2M')$, with $P_g \neq 0$. Let $\tau : \mathrm{SL}_2(\mathbb{Z}) \to (K \simeq_L K)$ be such that for every $\gamma \in \Gamma_0(M')$ the automorphism $\tau\gamma$ satisfies `IsLevelAutAt` for $\gamma^{-1}$ at parameters $(L,q,\zeta,q,q^2M',H)$: for all $k$, all such $f,g$ with integral $q$-expansions $p_f,p_g$ and $P_g \ne 0$, every $x \in K$ whose underlying Laurent series is the image of $P_f/P_g$, and every $\iota : L \to \mathbb{C}$ with $\iota\zeta = e^{2\pi i /q}$, one has $\iota(\tau x)\cdot q\text{-exp}(g\mid_k c_q(\gamma^{-1})) = q\text{-exp}(f\mid_k c_q(\gamma^{-1}))$, where $c_q(\gamma)$ denotes the matrix $\begin{pmatrix} a & b/q \\ qc & d\end{pmatrix}$ of `conjElemN`. The conclusion: for every $w \in K$, one has $\tau\gamma\, w = w$ for all $\gamma \in \Gamma_0(M')$ whose upper-right entry is divisible by $q$ if and only if the Laurent series underlying $w$ lies in the subfield of $\mathrm{LaurentSeries}\,L$ generated over $L$ by the coefficientwise images of the corresponding field of ratios of integral $q$-expansions of modular forms on $\Gamma_0(qM')$.
--
--   This identifies the common fixed field, inside the base-changed function field of level $\Gamma_H(q^2M')$, of the level automorphisms attached to the Borel-type condition $q \mid b$ on $\Gamma_0(M')$, as the base-changed function field of $\Gamma_0(qM')$; it is the case $q=3$, the twin statement for $q \ge 5$ being separate. It feeds the analysis of the covering of $\Gamma_0(qM')$-level by $\Gamma_H(q^2M')$-level function fields, used to show that the relevant prime has comap as prescribed, ramification index one and separable residue extension.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_forall_isLevelAutAt_apply_eq_of_dvd_iff_mem_laurentBaseChange_gamma0_mul_of_eq_three.lean

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_ModularCurve_FullLevelLevelAutAt

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups

theorem ModularCurve.FullLevel.forall_isLevelAutAt_apply_eq_of_dvd_iff_mem_laurentBaseChange_gamma0_mul_of_eq_three
    (q : ℕ) [Fact q.Prime] (hq3 : q = 3) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
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
      (∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 M' → (q : ℤ) ∣ (γ : Matrix (Fin 2) (Fin 2) ℤ) 0 1 → τ γ w = w) ↔
        ((w : ↥K) : LaurentSeries L) ∈
          ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 (q * M'))) := by sorry
