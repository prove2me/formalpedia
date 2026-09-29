-- Prove2me | Theorems.Thm_ModularCurve_exists_tendsto_realizeOf_mul_exp_of_not_mem_toValuationSubring
-- name    : ModularCurve.exists_tendsto_realizeOf_mul_exp_of_not_mem_toValuationSubring
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.061738+00:00
-- url     : https://prove2.me/theorems/8ab946e0-e067-54ac-b90a-97407421e88b
-- title:
--   Cusp places of X(Γ): width, ord_P y = -h, and limits
-- statement:
--   Let $\Gamma \le \mathrm{SL}_2(\mathbb{Z})$ be of finite index, containing the translation matrix `ModularGroup.T`, and satisfying the predicate `CongruenceSubgroup.IsCongruenceSubgroup`. Let $F_0$ be an intermediate field of $\mathbb{Q} \subset \mathbb{Q}((q))$ equal to `qExpFunctionFieldC ℚ Γ`, the subfield generated over $\mathbb{Q}$ by the quotients $p_f/p_g$ of integral $q$-expansions of pairs of modular forms of a common weight for $\Gamma$ (with $p_g \neq 0$), and let $F =$ `laurentBaseChange ℂ F₀` be the subfield of $\mathbb{C}((q))$ generated over $\mathbb{C}$ by the image of $F_0$ under the coefficientwise map induced by $\mathbb{Q} \to \mathbb{C}$. Let $y \in F$ have underlying Laurent series `jqModC ℂ`, namely $q^{-1}$ times the power series $E_4^3 \cdot \eta^{-24}$-type numerator `jNum` with coefficients mapped into $\mathbb{C}$, and assume the degree guard that $F$ has rank over $\mathbb{C}(y)$ equal to the index of $\Gamma \sqcup \langle -1\rangle$ in $\mathrm{SL}_2(\mathbb{Z})$. Finally let $P$ be a place of $F$ over $\mathbb{C}$, i.e. a proper valuation subring of $F$ containing $\mathbb{C}$ and a principal ideal ring, with $y \notin P$'s valuation subring. Then there exist $\sigma \in \mathrm{SL}_2(\mathbb{Z})$ and $h \in \mathbb{N}$ with $h > 0$ such that $\sigma T^h \sigma^{-1} \in \Gamma \sqcup \langle -1 \rangle$, $\operatorname{ord}_P(y) = -h$ (where $\operatorname{ord}_P$ is minus the logarithm of the adic valuation attached to $P$), and for every nonzero $x \in F$ there is $L \neq 0$ with $\operatorname{realizeOf}_\Gamma(x)(\sigma \cdot \tau)\, \exp(-2\pi i \operatorname{ord}_P(x) \tau / h) \to L$ as $\operatorname{Im} \tau \to \infty$; here $\operatorname{realizeOf}_\Gamma(x)$ is the function on $\mathbb{H}$ given by $g/h'$ for some pair of weight-$k$ forms $g,h'$ for $\Gamma$ with $x \cdot q\text{-exp}(h') = q\text{-exp}(g)$ and $h'$ nonvanishing at the point, and $0$ if no such pair exists.
--
--   This is the dictionary between places of the function field of $X(\Gamma)$ lying over the cusps and the cusps $\sigma\infty$ of $\mathbb{H}^*$: such a place is read off at some $\sigma \in \mathrm{SL}_2(\mathbb{Z})$, its width $h$ is the least positive exponent with $\sigma T^h\sigma^{-1} \in \pm\Gamma$, the order of $j$ at it is $-h$, and $\operatorname{ord}_P$ computes the leading exponent in the $q^{1/h}$-expansion of $x|\sigma$. It feeds the parity statement [`ModularCurve.even_ord_add_ord_of_not_mem_toValuationSubring_laurentBaseChange_gamma1`](thm.html#ModularCurve.even_ord_add_ord_of_not_mem_toValuationSubring_laurentBaseChange_gamma1) about orders at cusp places of $X_1(M)$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_tendsto_realizeOf_mul_exp_of_not_mem_toValuationSubring.lean

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_LaurentCoeff
import Definitions.Def_ModularCurve_QExpansionDiff
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_ModularCurve_ComplexPlaceDictionaryOf

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CongruenceSubgroup ModularCurve
open scoped MatrixGroups ModularForm

theorem ModularCurve.exists_tendsto_realizeOf_mul_exp_of_not_mem_toValuationSubring
    (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] (hT : ModularGroup.T ∈ Γ)
    (hΓ : CongruenceSubgroup.IsCongruenceSubgroup Γ)
    (F₀ : IntermediateField ℚ (LaurentSeries ℚ)) (hF : F₀ = ModularCurve.qExpFunctionFieldC ℚ Γ)
    (y : ↥(ModularCurve.laurentBaseChange ℂ F₀)) (hy : (y : LaurentSeries ℂ) = ModularCurve.jqModC ℂ)
    (hdeg : Module.finrank
        ↥(IntermediateField.adjoin ℂ ({y} : Set ↥(ModularCurve.laurentBaseChange ℂ F₀)))
        ↥(ModularCurve.laurentBaseChange ℂ F₀) =
      (Γ ⊔ Subgroup.zpowers (-1 : SL(2, ℤ))).index)
    (P : AlgebraicCurve.Place ℂ ↥(ModularCurve.laurentBaseChange ℂ F₀)) (hP : y ∉ P.toValuationSubring) :
    ∃ (σ : SL(2, ℤ)) (h : ℕ), 0 < h ∧
      σ * ModularGroup.T ^ h * σ⁻¹ ∈ Γ ⊔ Subgroup.zpowers (-1 : SL(2, ℤ)) ∧
      P.ord y = -(h : ℤ) ∧
      ∀ x : ↥(ModularCurve.laurentBaseChange ℂ F₀), x ≠ 0 → ∃ L : ℂ, L ≠ 0 ∧
        Filter.Tendsto
          (fun τ : UpperHalfPlane => ModularCurve.realizeOf Γ (x : LaurentSeries ℂ) (σ • τ) *
            Complex.exp (-(2 * Real.pi * Complex.I * (P.ord x : ℂ) * (τ : ℂ) / (h : ℂ))))
          UpperHalfPlane.atImInfty (nhds L) := by sorry
