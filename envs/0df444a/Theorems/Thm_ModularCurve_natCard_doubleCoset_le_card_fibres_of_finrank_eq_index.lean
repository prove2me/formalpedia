-- Prove2me | Theorems.Thm_ModularCurve_natCard_doubleCoset_le_card_fibres_of_finrank_eq_index
-- name    : ModularCurve.natCard_doubleCoset_le_card_fibres_of_finrank_eq_index
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.624895+00:00
-- url     : https://prove2.me/theorems/028fa6e7-01b7-5d70-8ba5-0d1fef0abfc1
-- title:
--   Lower bounds for the fibres of j over 0, 1728, ∞
-- statement:
--   Let $M$ be a nonzero natural number and $\Gamma\le \mathrm{SL}(2,\mathbb Z)$ a subgroup with $\Gamma_1(M)\le\Gamma$. Write $F(\Gamma)\subseteq\mathbb Q((q))$ for the subfield generated over $\mathbb Q$ by all quotients $\mathrm{intSeriesC}(p_f)/\mathrm{intSeriesC}(p_g)$ with $f,g$ modular forms of some common weight $k$ for $\Gamma$ (regarded inside $\mathrm{GL}(2,\mathbb R)$) admitting integral $q$-expansions $p_f,p_g\in\mathbb Z[[q]]$ and $\mathrm{intSeriesC}(p_g)\neq 0$, and let $F=\mathrm{laurentBaseChange}$ be the subfield of $\overline{\mathbb Q}((q))$ generated over $\overline{\mathbb Q}$ by the coefficientwise image of $F(\Gamma)$. Let $y\in F$ be an element whose underlying Laurent series is $\mathrm{jqModC}$, namely $q^{-1}$ times the power series $E_4^3\cdot\eta^{-24}$ over $\overline{\mathbb Q}$, i.e. the $q$-expansion of $j$. Assume the degree hypothesis $[F:\overline{\mathbb Q}(y)]=[\mathrm{SL}(2,\mathbb Z):\Gamma\cdot\{\pm 1\}]$, the index of $\Gamma\sqcup\langle -1\rangle$. Then three inequalities hold simultaneously, where places of $F$ over $\overline{\mathbb Q}$ are valuation subrings of $F$ containing $\overline{\mathbb Q}$, proper, with principal ideals, and $\mathrm{ord}$ is minus the logarithm of the associated adic valuation: the number of double cosets $\Gamma\backslash \mathrm{SL}(2,\mathbb Z)/\langle ST\rangle$ is at most the number of places $P$ with $\mathrm{ord}_P(y)>0$; the number of $\Gamma\backslash \mathrm{SL}(2,\mathbb Z)/\langle S\rangle$ is at most the number of places with $\mathrm{ord}_P(y-1728)>0$; and the number of $\Gamma\backslash \mathrm{SL}(2,\mathbb Z)/\langle T,-1\rangle$ is at most the number of places with $\mathrm{ord}_P(y)<0$.
--
--   Classically the fibres of $j\colon X(\Gamma)\to X(1)$ over $0$, $1728$ and $\infty$ are in bijection with the double coset spaces $\Gamma\backslash\mathrm{SL}(2,\mathbb Z)/\langle ST\rangle$, $\Gamma\backslash\mathrm{SL}(2,\mathbb Z)/\langle S\rangle$ and $\Gamma\backslash\mathrm{SL}(2,\mathbb Z)/\langle T,-1\rangle$, the stabilisers being those of $\rho$, $i$ and of the cusp $\infty$; here only the inequalities in one direction are asserted, for the $q$-expansion model of the function field over $\overline{\mathbb Q}$. It feeds the exact count of these fibres and, through it, the genus comparisons used for the modular curves of the Fermat argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_natCard_doubleCoset_le_card_fibres_of_finrank_eq_index.lean

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_AlgebraicCurve_DivisorClassGroup

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped MatrixGroups

theorem ModularCurve.natCard_doubleCoset_le_card_fibres_of_finrank_eq_index
    (M : ℕ) [NeZero M] (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ))
    (hΓ : CongruenceSubgroup.Gamma1 M ≤ Γ)
    (y : ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ Γ))
    (hy : (y : LaurentSeries (AlgebraicClosure ℚ)) = ModularCurve.jqModC (AlgebraicClosure ℚ))
    (hfull : Module.finrank
          (IntermediateField.adjoin (AlgebraicClosure ℚ)
            ({y} : Set (ModularCurve.laurentBaseChange (AlgebraicClosure ℚ)
              (ModularCurve.qExpFunctionFieldC ℚ Γ))))
          (ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ Γ)) =
        (Γ ⊔ Subgroup.zpowers (-1)).index) :
    Nat.card (DoubleCoset.Quotient (Γ : Set (Matrix.SpecialLinearGroup (Fin 2) ℤ))
        (Subgroup.zpowers (ModularGroup.S * ModularGroup.T) :
          Set (Matrix.SpecialLinearGroup (Fin 2) ℤ))) ≤
        Nat.card {P : AlgebraicCurve.Place (AlgebraicClosure ℚ)
          (ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ Γ)) //
            0 < P.ord y} ∧
      Nat.card (DoubleCoset.Quotient (Γ : Set (Matrix.SpecialLinearGroup (Fin 2) ℤ))
          (Subgroup.zpowers ModularGroup.S : Set (Matrix.SpecialLinearGroup (Fin 2) ℤ))) ≤
        Nat.card {P : AlgebraicCurve.Place (AlgebraicClosure ℚ)
          (ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ Γ)) //
            0 < P.ord (y - 1728)} ∧
      Nat.card (DoubleCoset.Quotient (Γ : Set (Matrix.SpecialLinearGroup (Fin 2) ℤ))
          ((Subgroup.zpowers ModularGroup.T ⊔ Subgroup.zpowers (-1) :
              Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)) :
            Set (Matrix.SpecialLinearGroup (Fin 2) ℤ))) ≤
        Nat.card {P : AlgebraicCurve.Place (AlgebraicClosure ℚ)
          (ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ Γ)) //
            P.ord y < 0} := by sorry
