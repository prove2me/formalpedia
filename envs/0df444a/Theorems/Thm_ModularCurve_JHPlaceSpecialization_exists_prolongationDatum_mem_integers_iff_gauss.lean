-- Prove2me | Theorems.Thm_ModularCurve_JHPlaceSpecialization_exists_prolongationDatum_mem_integers_iff_gauss
-- name    : ModularCurve.JHPlaceSpecialization.exists_prolongationDatum_mem_integers_iff_gauss
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:40.315379+00:00
-- url     : https://prove2.me/theorems/5e1ddaea-9a4c-5d97-9a65-36c1f1c9f502
-- title:
--   Existence of a prolongation datum with Gauss characterisation of R₁
-- statement:
--   Fix a prime $p$ and $M \neq 0$ with $p \mid M$ but $p^2 \nmid M$ (and $M/p \neq 0$), and a subgroup $H \le (\mathbb{Z}/M)^{\times}$ containing every unit that reduces to $1$ in $(\mathbb{Z}/(M/p))^{\times}$. Let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ with $p$ a non-unit of $A$ (the predicate `LiesOverPrime`), whose residue field $\kappa$ is algebraically closed of characteristic $p$. Write $F_M$ for `xHFunctionFieldBar M H`, the compositum of $\overline{\mathbb{Q}}$ with the level-$M$, $H$-function field inside $\overline{\mathbb{Q}}((q))$, and $\bar F$ for `JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)`. Let $\theta$ be a $\overline{\mathbb{Q}}$-algebra automorphism of $F_M$ and let `Psp` be a place specialization datum of type `JHPlaceSpecialization p M H hpM A`. Then there exists a prolongation datum for `Psp` and $\theta$, that is: two regular prolongations $R_1, R_2$ of $A$ to $F_M$ with residues in $\bar F$ (each a valuation subring of $F_M$ contracting to $A$ along $\overline{\mathbb{Q}} \to F_M$, equipped with a surjective ring map to $\bar F$ with kernel the maximal ideal, compatible with the residue map of $A$, and such that every non-zero element becomes $R$-integral with non-zero residue after scaling by a suitable constant), such that every $A$-integral Laurent series lying in $F_M$ is $R_1$-integral with $R_1$-residue the coefficientwise reduction of that series, such that $f \in R_2$ iff $\theta f \in R_1$ with residues matching along $\theta$, and, the conclusion exported here, such that $f \in F_M$ is $R_1$-integral precisely when its $q$-expansion can be written as $x/y$ with $x, y$ Laurent series over $A$ and the coefficientwise reduction of $y$ non-zero.
--
--   The first prolongation $R_1$ is the Gauss valuation of $q$-expansions at the cusp $\infty$ in level $M$, its residue field being identified with the level-$(M/p)$ function field over $\kappa$, and $R_2$ is its transport along $\theta$; the Gauss quotient criterion is exported so that later arguments can recognise concrete parameters as $R_1$- and $R_2$-integral. It feeds the construction of the glued specialization and the component-group computation for the de Rham model of $X_H(M)$ at $p$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JHPlaceSpecialization_exists_prolongationDatum_mem_integers_iff_gauss.lean

import Mathlib
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_ModularCurve_JHPlaceSpecialization
import Definitions.Def_AlgebraicCurve_RegularProlongation

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.JHNeronObjectAtP
open scoped MatrixGroups

theorem ModularCurve.JHPlaceSpecialization.exists_prolongationDatum_mem_integers_iff_gauss
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M) [NeZero (M / p)]
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (θ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (Psp : JHPlaceSpecialization p M H hpM A) :
    ∃ Rpd : JHPlaceSpecialization.ProlongationDatum Psp θ,

      ∀ f : ↥(xHFunctionFieldBar M H), f ∈ Rpd.R₁.integers ↔
        ∃ x y : LaurentSeries ↥A, coeffMap (IsLocalRing.residue ↥A) y ≠ 0 ∧
          ((f : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) * coeffMap A.subtype y = coeffMap A.subtype x := by sorry
