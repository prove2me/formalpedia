-- Prove2me | Theorems.Thm_ModularCurve_two_mul_genusFF_add_card_fibres_eq_finrank_add_two_of_gamma1_le
-- name    : ModularCurve.two_mul_genusFF_add_card_fibres_eq_finrank_add_two_of_gamma1_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:54.908972+00:00
-- url     : https://prove2.me/theorems/f1651288-3106-5b21-997e-5e33d77337df
-- title:
--   Fibre identity for j on X(Γ) over ℚ̄
-- statement:
--   Let $M$ be a nonzero natural number and let $\Gamma \le \mathrm{SL}_2(\mathbb{Z})$ contain $\Gamma_1(M)$. Write $F_0 =$ `qExpFunctionFieldC ℚ Γ` for the subfield of $\mathbb{Q}((q))$ generated over $\mathbb{Q}$ by all quotients $\iota(p_f)/\iota(p_g)$ of the integral $q$-expansions $p_f, p_g \in \mathbb{Z}[[q]]$ of two modular forms $f, g$ of the same weight $k$ for the image of $\Gamma$ in $\mathrm{GL}_2(\mathbb{R})$, with $\iota(p_g) \ne 0$, and let $F =$ `laurentBaseChange (AlgebraicClosure ℚ) F₀` be the subfield of $\overline{\mathbb{Q}}((q))$ generated over $k = \overline{\mathbb{Q}}$ by the coefficientwise image of $F_0$. Let $y \in F$ be an element whose underlying Laurent series is $q^{-1}E_4^3\eta^{-24}$, the $q$-expansion of $j$, with coefficients taken in $k$. Then, with $g =$ `genusFF` $(k, F)$ the repartition genus of $F/k$, places being valuation subrings of $F$ containing $k$, proper and principal, and $\mathrm{ord}_P$ the associated normalised valuation,
--   $$2g + \#\{P : \mathrm{ord}_P y < 0\} + \#\{P : \mathrm{ord}_P y > 0\} + \#\{P : \mathrm{ord}_P (y - 1728) > 0\} = [F : k(y)] + 2,$$
--   the last term being the $k(y)$-dimension of $F$, where $k(y) =$ `IntermediateField.adjoin k {y}`.
--
--   This is the Riemann–Hurwitz equality for the degree-$[F:k(y)]$ map $j : X(\Gamma) \to X(1)$ over $\overline{\mathbb{Q}}$, in the form which uses that $j$ is ramified only above $0$, $1728$ and $\infty$, so that each of the three fibres contributes its cardinality. It is the arithmetic input to the genus computations for full level and for $\Gamma_1(M)$, in particular to the genus formula relating $g$, the index of $\Gamma$ and the number of relevant double cosets.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_two_mul_genusFF_add_card_fibres_eq_finrank_add_two_of_gamma1_le.lean

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_AlgebraicCurve_Repartitions

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CongruenceSubgroup
open ModularCurve
open AlgebraicCurve
open scoped MatrixGroups

theorem ModularCurve.two_mul_genusFF_add_card_fibres_eq_finrank_add_two_of_gamma1_le
    (M : ℕ) [NeZero M] (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ))
    (hΓ : CongruenceSubgroup.Gamma1 M ≤ Γ)
    (y : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ)
          (ModularCurve.qExpFunctionFieldC ℚ Γ)))
    (hy : (y : LaurentSeries (AlgebraicClosure ℚ)) = ModularCurve.jqModC (AlgebraicClosure ℚ)) :
    2 * AlgebraicCurve.genusFF (AlgebraicClosure ℚ)
          ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ)
          (ModularCurve.qExpFunctionFieldC ℚ Γ)) +
        Nat.card {P : AlgebraicCurve.Place (AlgebraicClosure ℚ)
          ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ)
          (ModularCurve.qExpFunctionFieldC ℚ Γ)) // P.ord y < 0} +
        Nat.card {P : AlgebraicCurve.Place (AlgebraicClosure ℚ)
          ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ)
          (ModularCurve.qExpFunctionFieldC ℚ Γ)) // 0 < P.ord y} +
        Nat.card {P : AlgebraicCurve.Place (AlgebraicClosure ℚ)
          ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ)
          (ModularCurve.qExpFunctionFieldC ℚ Γ)) // 0 < P.ord (y - 1728)} =
      Module.finrank
          ↥(IntermediateField.adjoin (AlgebraicClosure ℚ)
            ({y} : Set ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ)
          (ModularCurve.qExpFunctionFieldC ℚ Γ))))
          ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ)
          (ModularCurve.qExpFunctionFieldC ℚ Γ)) + 2 := by sorry
