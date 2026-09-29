-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_Diamond_exists_modularForm_mul_qExpansion_eq_cuspPoint_and_slash_conjElemN_eq
-- name    : ModularCurve.FullLevel.Diamond.exists_modularForm_mul_qExpansion_eq_cuspPoint_and_slash_conjElemN_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:30.533368+00:00
-- url     : https://prove2.me/theorems/ebbc7c09-28fe-5dde-b88c-5e4eaa786139
-- title:
--   Tate q-torsion coordinates and c₄,c₆ via forms on Γ_{H_1}
-- statement:
--   Let $q$ be a prime, $M'\ge 1$ with $q\nmid M'$, and let $\ell_g$ be a prime with $\ell_g\equiv 11\pmod{12}$ and $\ell_g\mid M'$. Let $L$ be a field of characteristic zero containing a primitive $(q\ell_g)$-th root of unity $\xi$, and let $\iota:L\to\mathbb C$ be a ring homomorphism with $\iota(\xi)=\exp(2\pi i/(q\ell_g))$; write $\xi_u=\xi^{\ell_g}$ for the associated unit of $L$, a primitive $q$-th root of unity. Let $H_1\le(\mathbb Z/q^2M')^\times$ be the intersection of the kernel of reduction modulo $q$ with the kernel of reduction modulo $\ell_g$. The assertion is the existence of families $A_v$ (weight $6$), $B_v$ (weight $4$), $R_v$ (weight $3$) indexed by $v\in(\mathbb Z/q)^2$, and of single forms $C_4$ (weight $4$), $C_6$ (weight $6$), all modular for the subgroup of $\mathrm{SL}_2(\mathbb Z)$ consisting of the matrices of $\Gamma_0(q^2M')$ whose lower right entry reduces into $H_1$, viewed inside $\mathrm{GL}_2(\mathbb R)$, such that, writing $\hat q(\cdot)$ for the width-one $q$-expansion read as a Laurent series over $\mathbb C$ and $\iota_*$ for coefficientwise application of $\iota$ to Laurent series over $L$: for every $v\neq 0$, $\hat q(B_v)\neq 0$, $\hat q(B_v)$ lies in the image of $\iota_*$, $\iota_*\bigl(x_v+\tfrac1{12}\bigr)\cdot\hat q(B_v)=\hat q(A_v)$ and $\hat q(R_v)=\iota_*(2y_v+x_v)$, where $(x_v,y_v)$ is the cusp point attached to $v$ (the Tate toric point at $\xi_u^{v_0}$ when $v_1=0$, and the corresponding non-toric point otherwise); moreover $\hat q(C_4)=\iota_*(c_4)$ and $\hat q(C_6)=\iota_*(c_6)$ for the Tate curve $\mathrm{tateBase}\,L\,q$ over $L((\mathsf q))$; and for every $\rho=\begin{pmatrix}a&b\\c&d\end{pmatrix}\in\Gamma_0(M')$, with $\rho^{\sharp}=\bigl(\begin{smallmatrix}a&b/q\\qc&d\end{smallmatrix}\bigr)\in\mathrm{GL}_2(\mathbb R)$, one has $C_4\mid_4\rho^{\sharp}=C_4$, $C_6\mid_6\rho^{\sharp}=C_6$, and for all $v$, $A_v\mid_6\rho^{\sharp}=A_{(v_0d+v_1b,\;v_0c+v_1a)}$, and likewise $B_v\mid_4\rho^{\sharp}$ and $R_v\mid_3\rho^{\sharp}$ at the same permuted index (entries of $\rho$ read in $\mathbb Z/q$).
--
--   This is the level-$q$ realisation, on the group $\Gamma_{H_1}(q^2M')$ of the Diamond frame, of the coordinates of the $q$-torsion points $\zeta_q^{v_0}\mathsf q^{v_1}$ of the Tate curve with parameter $\mathsf q^{q}$, together with its invariants $c_4,c_6$, as (ratios of) $q$-expansions of holomorphic modular forms, with the index-permutation law for the conjugated action of $\Gamma_0(M')$. It is used by the lemmas identifying the level automorphisms attached to $\Gamma_0(M')$ on the $H_1$-level structures in terms of unit multiples and variable changes of the Tate curve.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_Diamond_exists_modularForm_mul_qExpansion_eq_cuspPoint_and_slash_conjElemN_eq.lean

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_XH
import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_ModularCurve_FullLevelLevelAutAt
import Definitions.Def_ModularCurve_TateSlots
import Definitions.Def_ModularCurve_KatzLevelPCusps
import Definitions.Def_ModularCurve_WeierstrassGamma0Pow

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups ModularForm

theorem ModularCurve.FullLevel.Diamond.exists_modularForm_mul_qExpansion_eq_cuspPoint_and_slash_conjElemN_eq
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (ℓg : ℕ) (hℓg : ℓg.Prime) (hℓg12 : ℓg % 12 = 11) (hℓgM' : ℓg ∣ M')
    (L : Type) [Field L] [CharZero L]
    (ξ : L) (hξ : IsPrimitiveRoot ξ (q * ℓg))
    (ι : L →+* ℂ) (hι : ι ξ = Complex.exp (2 * Real.pi * Complex.I / (q * ℓg)))
    (H₁ : Subgroup (ZMod (q ^ 2 * M'))ˣ)
    (hH₁ : H₁ = ModularCurve.FullLevel.levelH q M' ⊓ (ZMod.unitsMap (Dvd.dvd.mul_left hℓgM' (q ^ 2))).ker) :
    haveI : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
    letI ξu : Lˣ := (hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero hℓg.ne_zero)).unit ^ ℓg
    ∃ (Aw : (Fin 2 → ZMod q) → ModularForm (CohCarrier.GammaH (q ^ 2 * M') H₁ :
            Subgroup (GL (Fin 2) ℝ)) 6)
      (Bw : (Fin 2 → ZMod q) → ModularForm (CohCarrier.GammaH (q ^ 2 * M') H₁ :
            Subgroup (GL (Fin 2) ℝ)) 4)
      (Rw : (Fin 2 → ZMod q) → ModularForm (CohCarrier.GammaH (q ^ 2 * M') H₁ :
            Subgroup (GL (Fin 2) ℝ)) 3)
      (C4 : ModularForm (CohCarrier.GammaH (q ^ 2 * M') H₁ :
            Subgroup (GL (Fin 2) ℝ)) 4)
      (C6 : ModularForm (CohCarrier.GammaH (q ^ 2 * M') H₁ :
            Subgroup (GL (Fin 2) ℝ)) 6),
      (∀ v : Fin 2 → ZMod q, v ≠ 0 →
        HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 (⇑(Bw v))) ≠ 0 ∧
        (∃ b : LaurentSeries L, HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 (⇑(Bw v))) = ModularCurve.coeffMap ι b) ∧
        ModularCurve.coeffMap ι ((ModularCurve.cuspPoint L q ξu v).1 + HahnSeries.C ((12 : L)⁻¹)) *
            HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 (⇑(Bw v))) =
          HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 (⇑(Aw v))) ∧
        HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 (⇑(Rw v))) =
          ModularCurve.coeffMap ι (2 * (ModularCurve.cuspPoint L q ξu v).2 + (ModularCurve.cuspPoint L q ξu v).1)) ∧
      HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 (⇑C4)) =
        ModularCurve.coeffMap ι (ModularCurve.tateBase L q).c₄ ∧
      HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 (⇑C6)) =
        ModularCurve.coeffMap ι (ModularCurve.tateBase L q).c₆ ∧
      (∀ ρ : SL(2, ℤ), ρ ∈ CongruenceSubgroup.Gamma0 M' →
        (⇑C4 ∣[(4 : ℤ)] ModularCurve.FullLevel.conjElemN q ρ) = ⇑C4 ∧
        (⇑C6 ∣[(6 : ℤ)] ModularCurve.FullLevel.conjElemN q ρ) = ⇑C6 ∧
        ∀ v : Fin 2 → ZMod q,
          (⇑(Aw v) ∣[(6 : ℤ)] ModularCurve.FullLevel.conjElemN q ρ) = ⇑(Aw ![v 0 * ((ρ 1 1 : ℤ) : ZMod q) + v 1 * ((ρ 0 1 : ℤ) : ZMod q),
                  v 0 * ((ρ 1 0 : ℤ) : ZMod q) + v 1 * ((ρ 0 0 : ℤ) : ZMod q)]) ∧
          (⇑(Bw v) ∣[(4 : ℤ)] ModularCurve.FullLevel.conjElemN q ρ) = ⇑(Bw ![v 0 * ((ρ 1 1 : ℤ) : ZMod q) + v 1 * ((ρ 0 1 : ℤ) : ZMod q),
                  v 0 * ((ρ 1 0 : ℤ) : ZMod q) + v 1 * ((ρ 0 0 : ℤ) : ZMod q)]) ∧
          (⇑(Rw v) ∣[(3 : ℤ)] ModularCurve.FullLevel.conjElemN q ρ) = ⇑(Rw ![v 0 * ((ρ 1 1 : ℤ) : ZMod q) + v 1 * ((ρ 0 1 : ℤ) : ZMod q),
                  v 0 * ((ρ 1 0 : ℤ) : ZMod q) + v 1 * ((ρ 0 0 : ℤ) : ZMod q)])) := by sorry
