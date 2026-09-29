-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_Diamond_exists_variableChange_weightOne_tateBase_one_mem_laurentBaseChange_and_tateToricPoint_mem_of_ker
-- name    : ModularCurve.FullLevel.Diamond.exists_variableChange_weightOne_tateBase_one_mem_laurentBaseChange_and_tateToricPoint_mem_of_ker
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:30.533368+00:00
-- url     : https://prove2.me/theorems/3f92c9d6-9883-54c1-bc79-b7e49361940b
-- title:
--   Rationality of the weight-one twisted Tate model at diamond level
-- statement:
--   Fix a positive integer $M'$ and a prime $\ell$ with $\ell \equiv 11 \pmod{12}$ and $\ell \mid M'$. Let $L$ be a field of characteristic $0$, let $\zeta \in L$ be a primitive $\ell$-th root of unity, and assume there is a ring homomorphism $\iota : L \to \mathbb{C}$ with $\iota(\zeta) = e^{2\pi i/\ell}$. Let $K''$ be the intermediate field of $L \subseteq L((q))$ obtained as `laurentBaseChange`, i.e. the subfield generated over $L$ by the coefficientwise image under $\mathbb{Q} \to L$ of the $q$-expansion function field `xHFunctionField` of $X_H(M')$ for $H = \ker\bigl((\mathbb{Z}/M')^{\times} \to (\mathbb{Z}/\ell)^{\times}\bigr)$. Write $P_c = (x(P_c), y(P_c)) =$ `tateToricPoint L 1 c` for the toric point attached to a unit $c$, and `tateBase L 1` for the Tate Weierstrass curve over $L((q))$. The assertion is that there exists a Weierstrass variable change $C = (u, r, s, t)$ over $L((q))$ with $u \cdot (2x(P_{\zeta}) + \tfrac16) = 2y(P_{\zeta}) + x(P_{\zeta})$ and with $r, s, t$ the constant Laurent series $-\tfrac1{12}, -\tfrac12, \tfrac1{24}$, such that all five coefficients $a_1, a_2, a_3, a_4, a_6$ of $C \bullet$ `tateBase L 1` lie in $K''$, and such that for every $c \in L^{\times}$ with $c^{\ell} = 1$, $c \neq 1$, the transported coordinates $(u^{-1})^2 (x(P_c) - r)$ and $(u^{-1})^3 (y(P_c) - s(x(P_c) - r) - t)$ — the `xP` and `yP` fields of the `variableChange` by $C$ of the `LevelPData` with both points equal to $P_c$ — also lie in $K''$.
--
--   This is the level-$M'$ form of the statement that the weight-one twist of the Tate curve, normalised at the toric $\ell$-torsion point $P_{\zeta}$, together with the coordinates of all toric $\ell$-torsion points, is rational over the compositum of $L$ with the $q$-expansion function field of $X_H(M')$ for $H$ the kernel of $(\mathbb{Z}/M')^{\times} \to (\mathbb{Z}/\ell)^{\times}$, that is, for the group $\Gamma_0(M') \cap \Gamma_1(\ell)$. It feeds the construction of the étale/Tate model at diamond level used by [`ModularCurve.FullLevel.Diamond.exists_variableChange_raw_etale_tate_weightOne_level_fst_level_snd_fst_of_ker`](thm.html#ModularCurve.FullLevel.Diamond.exists_variableChange_raw_etale_tate_weightOne_level_fst_level_snd_fst_of_ker).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_Diamond_exists_variableChange_weightOne_tateBase_one_mem_laurentBaseChange_and_tateToricPoint_mem_of_ker.lean

import Mathlib
import Definitions.Def_ModularCurve_XH
import Definitions.Def_ModularCurve_TateSlots
import Definitions.Def_ModularCurve_KatzLevelP
import Definitions.Def_ModularCurve_KatzLevelPCusps

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups

theorem ModularCurve.FullLevel.Diamond.exists_variableChange_weightOne_tateBase_one_mem_laurentBaseChange_and_tateToricPoint_mem_of_ker
    (M' : ℕ) [NeZero M']
    (ℓg : ℕ) (hℓg : ℓg.Prime) (hℓg12 : ℓg % 12 = 11) (hℓgM' : ℓg ∣ M')
    (L : Type) [Field L] [CharZero L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ ℓg)
    (hιζ : ∃ ι : L →+* ℂ, ι ζ = Complex.exp (2 * Real.pi * Complex.I / ℓg))
    (K'' : IntermediateField L (LaurentSeries L))
    (hK'' : K'' = ModularCurve.laurentBaseChange L
      (ModularCurve.xHFunctionField M' (ZMod.unitsMap hℓgM').ker)) :
    ∃ C : WeierstrassCurve.VariableChange (LaurentSeries L),

      ((C.u : (LaurentSeries L)ˣ) : LaurentSeries L) *
          (2 * (ModularCurve.tateToricPoint L 1 (hζ.isUnit hℓg.ne_zero).unit).1 + HahnSeries.C ((6 : L)⁻¹)) =
        2 * (ModularCurve.tateToricPoint L 1 (hζ.isUnit hℓg.ne_zero).unit).2 + (ModularCurve.tateToricPoint L 1 (hζ.isUnit hℓg.ne_zero).unit).1 ∧
      C.r = HahnSeries.C (-(12 : L)⁻¹) ∧ C.s = HahnSeries.C (-(2 : L)⁻¹) ∧ C.t = HahnSeries.C ((24 : L)⁻¹) ∧

      (C • ModularCurve.tateBase L 1).a₁ ∈ Set.range ((↑) : ↥K'' → LaurentSeries L) ∧
      (C • ModularCurve.tateBase L 1).a₂ ∈ Set.range ((↑) : ↥K'' → LaurentSeries L) ∧
      (C • ModularCurve.tateBase L 1).a₃ ∈ Set.range ((↑) : ↥K'' → LaurentSeries L) ∧
      (C • ModularCurve.tateBase L 1).a₄ ∈ Set.range ((↑) : ↥K'' → LaurentSeries L) ∧
      (C • ModularCurve.tateBase L 1).a₆ ∈ Set.range ((↑) : ↥K'' → LaurentSeries L) ∧

      (∀ c : Lˣ, c ^ ℓg = 1 → c ≠ 1 →
        ((⟨(ModularCurve.tateToricPoint L 1 c).1, (ModularCurve.tateToricPoint L 1 c).2, (ModularCurve.tateToricPoint L 1 c).1, (ModularCurve.tateToricPoint L 1 c).2⟩ :
            ModularCurve.LevelPData (LaurentSeries L)).variableChange C).xP ∈ Set.range ((↑) : ↥K'' → LaurentSeries L) ∧
        ((⟨(ModularCurve.tateToricPoint L 1 c).1, (ModularCurve.tateToricPoint L 1 c).2, (ModularCurve.tateToricPoint L 1 c).1, (ModularCurve.tateToricPoint L 1 c).2⟩ :
            ModularCurve.LevelPData (LaurentSeries L)).variableChange C).yP ∈ Set.range ((↑) : ↥K'' → LaurentSeries L)) := by sorry
