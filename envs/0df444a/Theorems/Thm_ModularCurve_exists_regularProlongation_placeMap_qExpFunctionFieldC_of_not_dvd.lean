-- Prove2me | Theorems.Thm_ModularCurve_exists_regularProlongation_placeMap_qExpFunctionFieldC_of_not_dvd
-- name    : ModularCurve.exists_regularProlongation_placeMap_qExpFunctionFieldC_of_not_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:51.361078+00:00
-- url     : https://prove2.me/theorems/1bacdbdb-f189-51ae-9890-03c506aad278
-- title:
--   Good reduction of ℚ̄· F(Γ) at a place above p∤ M
-- statement:
--   Fix $M\ge 1$ and a subgroup $\Gamma\le \mathrm{SL}_2(\mathbb{Z})$ with $\Gamma_1(M)\le\Gamma\le\Gamma_0(M)$, a prime $p$ with $p\nmid M$, and a valuation subring $A$ of $\overline{\mathbb{Q}}$ lying over $p$ in the sense that $p$ is a non-unit of $A$, whose residue field $\kappa=\mathrm{ResidueField}\,A$ is algebraically closed. Write $F'=\mathrm{laurentBaseChange}\,\overline{\mathbb{Q}}\,(\mathrm{qExpFunctionFieldC}\,\mathbb{Q}\,\Gamma)$, the subfield of $\overline{\mathbb{Q}}((q))$ generated over $\overline{\mathbb{Q}}$ by the coefficientwise images of $\mathrm{qExpFunctionFieldC}\,\mathbb{Q}\,\Gamma$, and $\bar F=\mathrm{qExpFunctionFieldC}\,\kappa\,\Gamma$, the subfield of $\kappa((q))$ generated over $\kappa$ by the quotients $\mathrm{intSeriesC}\,\kappa\,p_f/\mathrm{intSeriesC}\,\kappa\,p_g$ of integral $q$-expansions of modular forms for $\Gamma$. The assertion is that there exist a regular prolongation $R$ of $A$ from $\overline{\mathbb{Q}}$ to $F'$ with residue field $\bar F$ — that is, a valuation subring $R.\mathrm{integers}$ of $F'$ contracting to $A$ on $\overline{\mathbb{Q}}$, together with a surjective ring homomorphism $R.\mathrm{residue}$ onto $\bar F$ with kernel the maximal ideal, compatible with reduction on $A$, and such that every nonzero element of $F'$ has a nonzero reduction after scaling by a constant — and a map $r$ from places of $F'/\overline{\mathbb{Q}}$ to places of $\bar F/\kappa$ (places being proper valuation subrings containing the constants which are principal ideal rings), such that: (i) for every Laurent series $y$ with coefficients in $A$ whose image in $\overline{\mathbb{Q}}((q))$ lies in $F'$, that image lies in $R.\mathrm{integers}$ and its residue, read inside $\kappa((q))$, is the coefficientwise reduction of $y$; and (ii) for every $f\in R.\mathrm{integers}$ with $R.\mathrm{residue}\,f\ne 0$ and every divisor $D$ on $F'$ with $D(P)=\mathrm{ord}_P(f)$ for all places $P$, the pushforward $r_*D$ satisfies $(r_*D)(Q)=\mathrm{ord}_Q(R.\mathrm{residue}\,f)$ for every place $Q$ of $\bar F$, where $\mathrm{ord}$ is minus the logarithm of the associated adic valuation.
--
--   This is the statement that the modular function field of level $\Gamma$ has good reduction at a place of $\overline{\mathbb{Q}}$ above a prime $p\nmid M$, in the form of a regular prolongation whose reduction map is coefficientwise reduction of $A$-integral $q$-expansions, together with a reduction map on places carrying principal divisors to principal divisors. It is used in the reduction of differentials of the first kind, namely by [`ModularCurve.exists_mem_regularDifferentials_qExpFunctionFieldC_residueField_of_mem_regularDifferentials`](thm.html#ModularCurve.exists_mem_regularDifferentials_qExpFunctionFieldC_residueField_of_mem_regularDifferentials).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_regularProlongation_placeMap_qExpFunctionFieldC_of_not_dvd.lean

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_QExpansionDiff
import Definitions.Def_AlgebraicCurve_RegularDifferentials
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_FLTPrelim_Modularity
import Definitions.Def_FLTPrelim_Ramification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups
open AlgebraicCurve IsLocalRing
open ModularCurve

set_option synthInstance.maxHeartbeats 400000 in

theorem ModularCurve.exists_regularProlongation_placeMap_qExpFunctionFieldC_of_not_dvd
    (M : ℕ) [NeZero M] (Γ : Subgroup SL(2, ℤ))
    (hΓ₁ : CongruenceSubgroup.Gamma1 M ≤ Γ) (hΓ₀ : Γ ≤ CongruenceSubgroup.Gamma0 M)
    (p : ℕ) [Fact p.Prime] (hpM : ¬ p ∣ M)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [IsAlgClosed (ResidueField ↥A)] :
    ∃ (R : RegularProlongation A ↥(laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ Γ))
          ↥(qExpFunctionFieldC (ResidueField ↥A) Γ))
      (r : Place (AlgebraicClosure ℚ) ↥(laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ Γ))
          → Place (ResidueField ↥A) ↥(qExpFunctionFieldC (ResidueField ↥A) Γ)),
      (∀ (y : LaurentSeries ↥A)
          (hy : coeffMap A.subtype y ∈ laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ Γ)),
        ∃ hint : (⟨coeffMap A.subtype y, hy⟩ : ↥(laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ Γ))) ∈ R.integers,
          ((R.residue ⟨_, hint⟩ : ↥(qExpFunctionFieldC (ResidueField ↥A) Γ)) : LaurentSeries (ResidueField ↥A))
            = coeffMap (residue ↥A) y)
      ∧ ∀ f : R.integers, R.residue f ≠ 0 →
          ∀ D : Divisor (AlgebraicClosure ℚ) ↥(laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ Γ)),
            (∀ P, D P = P.ord (f : ↥(laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ Γ)))) →
          ∀ Q, Finsupp.mapDomain r D Q = Q.ord (R.residue f) := by sorry
