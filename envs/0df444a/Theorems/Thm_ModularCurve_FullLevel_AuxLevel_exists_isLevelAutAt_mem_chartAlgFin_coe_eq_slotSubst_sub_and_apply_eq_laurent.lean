-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_AuxLevel_exists_isLevelAutAt_mem_chartAlgFin_coe_eq_slotSubst_sub_and_apply_eq_laurent
-- name    : ModularCurve.FullLevel.AuxLevel.exists_isLevelAutAt_mem_chartAlgFin_coe_eq_slotSubst_sub_and_apply_eq_laurent
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:22.181174+00:00
-- url     : https://prove2.me/theorems/0db2a127-31ee-51e4-bd8b-7f57537bcbff
-- title:
--   A level automorphism and a chart element with Tate-slot expansions
-- statement:
--   Let $q$ be a prime with $5 \le q$, let $M'$ be a non-zero natural number with $q \nmid M'$, and let $\ell$ be a prime with $3 \le \ell$, $\ell \ne q$, $\ell \nmid M'$. Let $L$ be a field of characteristic zero which is a cyclotomic extension of $\mathbb{Q}$ of level $\{q\ell\}$, let $\zeta \in L$ be a primitive $q$-th and $\xi \in L$ a primitive $q\ell$-th root of unity. Let $K$ be the intermediate field of $L \subseteq \operatorname{LaurentSeries} L$ obtained as [`ModularCurve.laurentBaseChange`](def/ModularCurve_LaurentCoeff.html#L103), i.e. generated over $L$ by the coefficientwise image along $\mathbb{Q} \to L$ of [`ModularCurve.xHFunctionField`](def/ModularCurve_XH.html#L79) of level $(q\ell)^2 M'$ for the subgroup $\mathrm{levelH}(q\ell)(M') = \ker\big((\mathbb{Z}/(q\ell)^2M')^\times \to (\mathbb{Z}/q\ell)^\times\big)$. Let $A$ be a discrete valuation domain with an $L$-algebra structure making $L$ its fraction field, with $q \in \mathfrak{m}_A$ and $\zeta$ in the image of $A$, with a compatible $A$-algebra structure on $K$; let $j \in K$, $j \ne 0$, have Laurent expansion the coefficient embedding of $\mathsf{q}^{-1}\cdot \mathrm{jNumQ}$, and let $\varpi$ generate $\mathfrak{m}_A$. Then there exist $\gamma \in \mathrm{SL}_2(\mathbb{Z})$ lying in $\Gamma(\ell)$ and in $\Gamma_0(M')$, an $L$-algebra automorphism $\tau$ of $K$ satisfying `IsLevelAutAt` for $\gamma^{-1}$ (for every weight $k$, every pair $f,g$ of modular forms for $\Gamma_H((q\ell)^2M')$ with integral $\mathsf{q}$-expansions $p_f,p_g$, $p_g$ with non-zero associated series, and every $x \in K$ expanding as the image of $p_f/p_g$, and every $\iota : L \to \mathbb{C}$ with $\iota\xi = e^{2\pi i/(q\ell)}$, the series $\iota(\tau x)$ times the $\mathsf{q}$-expansion of $g\mid_k \mathrm{conjElemN}(q\ell)(\gamma^{-1})$ equals that of $f\mid_k \mathrm{conjElemN}(q\ell)(\gamma^{-1})$), an element $H$ of `chartAlgFin` $A$ $K$ $j$, that is integral over $A[j]$, Laurent series $u_1,u_2$ over $L$, units $\zeta', c_1, c_2 \in A^\times$ and naturals $j_1, j_2$ with the following properties: each $u_i$ is a ratio $\hat x/\hat y$ of images in $L((\mathsf{q}))$ of power series $x, y$ over $A$ whose reductions modulo $\mathfrak{m}_A$ are non-zero (stated as $u_i \hat y = \hat x$); $\zeta' - 1 \in \mathfrak{m}_A$; $0 < j_1, j_2 < q\ell$, $2j_1 \ne q\ell$, $2j_2 \ne q\ell$ and $\min(j_1, q\ell - j_1) \ne \min(j_2, q\ell - j_2)$; and, writing $X(c,i)$ for [`ModularCurve.slotSubst`](def/ModularCurve_TateSlots.html#L31) $A\,(q\ell)\,c\,i$ applied to the two-variable series `tateUnivX` with coefficients pushed along $A \to L$, the Laurent expansions satisfy $H = u_1\,\big(X(\zeta'c_1, j_1) - X(c_1,j_1)\big)$ and $\tau(H) = u_2\,\big(X(c_2,j_2) - X(c_1,j_1)\big)$.
--
--   This is the existence step of the auxiliary-level construction: it produces simultaneously a Galois-theoretic automorphism of the full-level function field attached to a matrix in $\Gamma(\ell) \cap \Gamma_0(M')$ and an element of the $j$-finite chart algebra whose $\mathsf{q}$-expansion, and that of its image under the automorphism, are differences of $X$-coordinates of points of the Tate curve in two distinct slots, up to Gauss units. It is used in the subsequent statement that such an $H$ lies in the non-units of the Gauss valuation subring while its image under the automorphism does not, the separation being exactly what the inequality $\min(j_1, q\ell - j_1) \ne \min(j_2, q\ell - j_2)$ encodes.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_AuxLevel_exists_isLevelAutAt_mem_chartAlgFin_coe_eq_slotSubst_sub_and_apply_eq_laurent.lean

import Mathlib
import Definitions.Def_ModularCurve_TateSlots
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_DrinfeldCurve_LocalChart
import Definitions.Def_ModularCurve_FullLevelLevelAutAt

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

open scoped MatrixGroups

theorem ModularCurve.FullLevel.AuxLevel.exists_isLevelAutAt_mem_chartAlgFin_coe_eq_slotSubst_sub_and_apply_eq_laurent
    (q : ℕ) [Fact q.Prime] (hq : 5 ≤ q) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ3 : 3 ≤ ℓ) (hℓq : ℓ ≠ q) (hℓM' : ¬ ℓ ∣ M')
    (L : Type) [Field L] [CharZero L] [IsCyclotomicExtension {q * ℓ} ℚ L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ q)
    (ξ : L) (hξ : IsPrimitiveRoot ξ (q * ℓ))
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L
      (ModularCurve.xHFunctionField ((q * ℓ) ^ 2 * M')
        (ModularCurve.FullLevel.levelH (q * ℓ) M')))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAq : (q : A) ∈ IsLocalRing.maximalIdeal A) (hζA : ∃ x : A, algebraMap A L x = ζ)
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)]
    (ϖ : A) (hϖ : IsLocalRing.maximalIdeal A = Ideal.span {ϖ}) :
    ∃ (γ : SL(2, ℤ)) (_ : γ ∈ CongruenceSubgroup.Gamma ℓ) (_ : γ ∈ CongruenceSubgroup.Gamma0 M')
      (τ : ↥K ≃ₐ[L] ↥K) (_ : ModularCurve.FullLevel.IsLevelAutAt L (q * ℓ) ξ (q * ℓ) ((q * ℓ) ^ 2 * M')
        (ModularCurve.FullLevel.levelH (q * ℓ) M') γ⁻¹ K τ)
      (H : ↥K) (_ : H ∈ AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)
      (u₁ u₂ : LaurentSeries L) (ζ' c₁ c₂ : Aˣ) (j₁ j₂ : ℕ),

      (∃ x y : PowerSeries A, x.map (IsLocalRing.residue A) ≠ 0 ∧ y.map (IsLocalRing.residue A) ≠ 0 ∧
        u₁ * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap A L)) =
          HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L))) ∧
      (∃ x y : PowerSeries A, x.map (IsLocalRing.residue A) ≠ 0 ∧ y.map (IsLocalRing.residue A) ≠ 0 ∧
        u₂ * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap A L)) =
          HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L))) ∧
      ((ζ' : A) - 1) ∈ IsLocalRing.maximalIdeal A ∧
      0 < j₁ ∧ j₁ < q * ℓ ∧ 0 < j₂ ∧ j₂ < q * ℓ ∧ 2 * j₁ ≠ q * ℓ ∧ 2 * j₂ ≠ q * ℓ ∧
      min j₁ (q * ℓ - j₁) ≠ min j₂ (q * ℓ - j₂) ∧
      ((H : ↥K) : LaurentSeries L) = u₁ *
        HahnSeries.ofPowerSeries ℤ L ((ModularCurve.slotSubst A (q * ℓ) (ζ' * c₁) j₁ ModularCurve.tateUnivX -
          ModularCurve.slotSubst A (q * ℓ) c₁ j₁ ModularCurve.tateUnivX).map (algebraMap A L)) ∧
      ((τ H : ↥K) : LaurentSeries L) = u₂ *
        HahnSeries.ofPowerSeries ℤ L ((ModularCurve.slotSubst A (q * ℓ) c₂ j₂ ModularCurve.tateUnivX -
          ModularCurve.slotSubst A (q * ℓ) c₁ j₁ ModularCurve.tateUnivX).map (algebraMap A L)) := by sorry
