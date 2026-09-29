-- Prove2me | Theorems.Thm_ModularCurve_JHPlaceSpecialization_exists_regularProlongation_mem_integers_iff_gauss_and_residue_coeffMap
-- name    : ModularCurve.JHPlaceSpecialization.exists_regularProlongation_mem_integers_iff_gauss_and_residue_coeffMap
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:40.315379+00:00
-- url     : https://prove2.me/theorems/5b12af58-db19-5974-bc2e-9ed8c9ee86aa
-- title:
--   Gauss prolongation to the level-M modular function field
-- statement:
--   Let $p$ be a prime and $M$ a non-zero natural number, let $H$ be a subgroup of $(\mathbb{Z}/M)^\times$, and assume $p \mid M$ but $p^2 \nmid M$ (with $M/p$ non-zero), and that $H$ contains every unit $u$ of $\mathbb{Z}/M$ whose image under the reduction map `ZMod.unitsMap` for $M/p \mid M$ is $1$. Let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ with $p$ a non-unit of $A$ (the predicate `LiesOverPrime p`), whose residue field $\kappa$ has characteristic $p$ and is algebraically closed. Write $F_M =$ `xHFunctionFieldBar M H`, the base change to $\overline{\mathbb{Q}}$ of the $q$-expansion function field of level $\Gamma_H(M)$, an intermediate field of $\overline{\mathbb{Q}} \subset \overline{\mathbb{Q}}((q))$. Then there is a regular prolongation $R_1$ of $A$ to $F_M$ with residue field `JHNeronObjectAtP.Fbar p M H hpM` $\kappa$, the field `qExpFunctionFieldC` $\kappa$ `(ΓN p M H hpM)` of $q$-expansions over $\kappa$ — that is, a valuation subring $R_1.\mathrm{integers}$ of $F_M$ whose contraction along $\overline{\mathbb{Q}} \to F_M$ is exactly $A$, together with a surjective ring homomorphism $R_1.\mathrm{residue}$ onto that field whose kernel is the maximal ideal, compatible with the residue map of $A$, and such that every non-zero $f \in F_M$ has a scalar multiple $c \cdot f$ lying in $R_1.\mathrm{integers}$ with non-zero residue — satisfying two further properties: (i) (Gauss criterion) for $f \in F_M$, one has $f \in R_1.\mathrm{integers}$ if and only if there are Laurent series $x, y$ over $A$ with the coefficientwise reduction of $y$ to $\kappa((q))$ non-zero and $f \cdot y = x$ in $\overline{\mathbb{Q}}((q))$ (coefficients of $x,y$ pushed forward along $A \hookrightarrow \overline{\mathbb{Q}}$); and (ii) for every Laurent series $y$ over $A$ whose image in $\overline{\mathbb{Q}}((q))$ lies in $F_M$, that element belongs to $R_1.\mathrm{integers}$ and its $R_1$-residue is, as a Laurent series over $\kappa$, the coefficientwise reduction of $y$.
--
--   This provides the Gauss (coefficientwise) prolongation of a place of $\overline{\mathbb{Q}}$ above $p$ to the function field of $X_H(M)$ in the case $p \parallel M$, with the two properties that pin it down: its integers are the Gauss-integral $q$-expansions, and on $A$-integral $q$-expansions the residue map is reduction of coefficients, landing in the $q$-expansion field of the lowered level over $\kappa$. It is the source of the prolongation datum for $X_H(M)$ at $p$ (including the Atkin–Lehner transported prolongation) and of the Gauss characterisation used in the de Rham model of $X_H$ at $p$ and in the analysis of crossing primes.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JHPlaceSpecialization_exists_regularProlongation_mem_integers_iff_gauss_and_residue_coeffMap.lean

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

theorem ModularCurve.JHPlaceSpecialization.exists_regularProlongation_mem_integers_iff_gauss_and_residue_coeffMap
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M) [NeZero (M / p)]
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)] :
    ∃ R₁ : RegularProlongation A ↥(xHFunctionFieldBar M H) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)),

      (∀ f : ↥(xHFunctionFieldBar M H), f ∈ R₁.integers ↔
        ∃ x y : LaurentSeries ↥A, coeffMap (IsLocalRing.residue ↥A) y ≠ 0 ∧
          ((f : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) * coeffMap A.subtype y = coeffMap A.subtype x) ∧

      (∀ (y : LaurentSeries ↥A) (hy : coeffMap A.subtype y ∈ xHFunctionFieldBar M H),
        ∃ h : (⟨coeffMap A.subtype y, hy⟩ : ↥(xHFunctionFieldBar M H)) ∈ R₁.integers,
          ((R₁.residue ⟨_, h⟩ : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) : LaurentSeries (ResidueField ↥A)) = coeffMap (IsLocalRing.residue ↥A) y) := by sorry
