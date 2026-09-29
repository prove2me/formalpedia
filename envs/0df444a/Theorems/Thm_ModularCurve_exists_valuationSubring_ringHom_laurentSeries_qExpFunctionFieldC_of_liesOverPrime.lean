-- Prove2me | Theorems.Thm_ModularCurve_exists_valuationSubring_ringHom_laurentSeries_qExpFunctionFieldC_of_liesOverPrime
-- name    : ModularCurve.exists_valuationSubring_ringHom_laurentSeries_qExpFunctionFieldC_of_liesOverPrime
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.061738+00:00
-- url     : https://prove2.me/theorems/25347b0a-7962-59be-8690-f1e724078f45
-- title:
--   Gauss valuation ring and coefficientwise reduction of q-expansion fields
-- statement:
--   Let $\Gamma\le\mathrm{SL}_2(\mathbb Z)$ be of finite index with $T\in\Gamma$, let $p$ be a prime, and write $F=\mathrm{qExpFunctionFieldC}\,\mathbb Q\,\Gamma$ for the subfield of $\mathbb Q((q))$ generated over $\mathbb Q$ by the quotients of integral $q$-expansions of two modular forms of equal weight for $\Gamma$ (denominator nonzero). Let $j\in F$ have underlying Laurent series `jqModC ℚ` $=q^{-1}\cdot(E_4^3\cdot\eta^{-24}$ reduced to $\mathbb Q)$. Let $A$ be a valuation subring of $\overline{\mathbb Q}$ with $p$ a nonunit of $A$, let $\kappa$ be its residue field, let $\rho_0$ be a ring map from $\mathbb Z_{(p)}=\{x\in\mathbb Q:\ p\nmid\operatorname{den}x\}$ to $A$ whose composite with the inclusion $A\hookrightarrow\overline{\mathbb Q}$ is the structure map, and let $x\in\mathrm{qExpFunctionFieldC}\,\kappa\,\Gamma$ have series `jqModC` over $\kappa$. With $\kappa$ an $\mathbb Z_{(p)}$-algebra via $\rho_0$ followed by reduction, the assertion is the existence of a valuation subring $V$ of $F$ containing the image of $\mathbb Z_{(p)}$ and a ring homomorphism $\rho\colon V\to\kappa((q))$ such that: $p$ is a nonunit of $V$; for every $P\in\mathbb Z_{(p)}[X]$ not divisible by the constant $p$, both $P(j)$ and $P(j)^{-1}$ lie in $V$; $\rho$ vanishes on the nonunits of $V$; $\rho$ agrees on $\mathbb Z_{(p)}$ with $\mathbb Z_{(p)}\to\kappa\to\kappa((q))$; $\rho(j)=$ `jqModC` over $\kappa$; the subfield of $\kappa((q))$ generated over $\kappa$ by the range of $\rho$ is exactly $\mathrm{qExpFunctionFieldC}\,\kappa\,\Gamma$; $f\in F$ lies in $V$ precisely when there are $y,z\in A((q))$ with $y$ having nonzero coefficientwise reduction and $f\cdot y=z$ in $\overline{\mathbb Q}((q))$; and for any such presentation of $v\in V$ one has $\rho(v)\cdot\bar y=\bar z$ in $\kappa((q))$.
--
--   This packages the $(p)$-adic Gauss valuation on the field of $q$-expansions of modular functions for $\Gamma$, together with coefficientwise reduction of $q$-expansions at a place of $\overline{\mathbb Q}$ above $p$, in the form of reduction of algebraic function fields modulo a prime of the constant field in the sense of Deuring and Igusa; membership in $V$ and the values of $\rho$ are characterised by the Gauss condition in $A((q))$. It is obtained from the regular-prolongation statement for the base change of $F$ to $\overline{\mathbb Q}$, and serves as the input for the construction of models of modular curves at $p$ and of the associated reduction maps on function fields and differentials.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_valuationSubring_ringHom_laurentSeries_qExpFunctionFieldC_of_liesOverPrime.lean

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_GaloisRep_Flat

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups
open ModularCurve IsLocalRing

set_option synthInstance.maxHeartbeats 400000 in

theorem ModularCurve.exists_valuationSubring_ringHom_laurentSeries_qExpFunctionFieldC_of_liesOverPrime
    (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] (hT : ModularGroup.T ∈ Γ) (p : ℕ) [Fact p.Prime]
    (j : ↥(qExpFunctionFieldC ℚ Γ)) (hj : (j : LaurentSeries ℚ) = jqModC ℚ)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (ρ₀ : ↥(GaloisRep.ratLocalizedAt p) →+* ↥A)
    (hρ₀ : A.subtype.comp ρ₀ = algebraMap ↥(GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ))
    (x : ↥(qExpFunctionFieldC (ResidueField ↥A) Γ))
    (hx : (x : LaurentSeries (ResidueField ↥A)) = jqModC (ResidueField ↥A)) :
    letI := ((residue ↥A).comp ρ₀).toAlgebra
    ∃ (V : ValuationSubring ↥(qExpFunctionFieldC ℚ Γ))
      (hRV : ∀ r : ↥(GaloisRep.ratLocalizedAt p), algebraMap ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ Γ) r ∈ V)
      (ρ : ↥V →+* LaurentSeries (ResidueField ↥A)),
      algebraMap ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ Γ) (p : ↥(GaloisRep.ratLocalizedAt p)) ∈ V.nonunits ∧
      (∀ P : Polynomial ↥(GaloisRep.ratLocalizedAt p), ¬ (Polynomial.C (p : ↥(GaloisRep.ratLocalizedAt p)) ∣ P) →
        Polynomial.aeval j P ∈ V ∧ (Polynomial.aeval j P)⁻¹ ∈ V) ∧
      (∀ v : ↥V, (v : ↥(qExpFunctionFieldC ℚ Γ)) ∈ V.nonunits → ρ v = 0) ∧
      (∀ r : ↥(GaloisRep.ratLocalizedAt p),
        ρ ⟨algebraMap ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ Γ) r, hRV r⟩ =
          algebraMap (ResidueField ↥A) (LaurentSeries (ResidueField ↥A))
            (algebraMap ↥(GaloisRep.ratLocalizedAt p) (ResidueField ↥A) r)) ∧
      (∀ v : ↥V, (v : ↥(qExpFunctionFieldC ℚ Γ)) = j → ρ v = jqModC (ResidueField ↥A)) ∧
      IntermediateField.adjoin (ResidueField ↥A) (Set.range ρ) = qExpFunctionFieldC (ResidueField ↥A) Γ ∧
      (∀ f : ↥(qExpFunctionFieldC ℚ Γ), f ∈ V ↔
        ∃ y z : LaurentSeries ↥A, coeffMap (residue ↥A) y ≠ 0 ∧
          coeffEmb (AlgebraicClosure ℚ) ((f : ↥(qExpFunctionFieldC ℚ Γ)) : LaurentSeries ℚ) * coeffMap A.subtype y =
            coeffMap A.subtype z) ∧
      (∀ (v : ↥V) (y z : LaurentSeries ↥A), coeffMap (residue ↥A) y ≠ 0 →
          coeffEmb (AlgebraicClosure ℚ) (((v : ↥(qExpFunctionFieldC ℚ Γ)) : LaurentSeries ℚ)) * coeffMap A.subtype y =
            coeffMap A.subtype z →
        ρ v * coeffMap (residue ↥A) y = coeffMap (residue ↥A) z) := by sorry
