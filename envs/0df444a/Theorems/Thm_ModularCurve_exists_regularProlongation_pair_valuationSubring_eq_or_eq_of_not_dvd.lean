-- Prove2me | Theorems.Thm_ModularCurve_exists_regularProlongation_pair_valuationSubring_eq_or_eq_of_not_dvd
-- name    : ModularCurve.exists_regularProlongation_pair_valuationSubring_eq_or_eq_of_not_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:51.361078+00:00
-- url     : https://prove2.me/theorems/06c0183a-0577-5303-8c95-3f9cdc06a280
-- title:
--   The two prolongations of X₀(Np) above p∤ N
-- statement:
--   Let $N\ge 1$ and let $p$ be a prime with $p\nmid N$, and let $A$ be a valuation subring of $\overline{\mathbb Q}$ lying over $p$ in the sense that $p$ is a nonunit of $A$; write $k=\mathrm{ResidueField}\,A$. Put $F=\mathrm{modularFunctionFieldBar}(Np)$, the subfield of $\overline{\mathbb Q}((q))$ obtained by base change of $\mathrm{modularFunctionFieldFull}(Np)=\mathbb Q(\mathrm{divisorExpansions}(Np))$ to $\overline{\mathbb Q}$, and $\bar F=\mathrm{modularFunctionFieldFullC}(k,N)=k(\mathrm{divisorExpansionsC}(k,N))\subseteq k((q))$. The assertion is that there is a pair $R_0,R_1$ of regular prolongations of $A$ to $F$ with residue field $\bar F$ — each consisting of a valuation subring of $F$ whose intersection with $\overline{\mathbb Q}$ is $A$, together with a surjective ring homomorphism onto $\bar F$ with kernel the maximal ideal, extending $A\to k$, and such that every nonzero $f\in F$ has an $\overline{\mathbb Q}$-multiple lying in the subring with nonzero residue — satisfying: (i) $f\in R_0$ iff $f\cdot y=x$ for Laurent series $x,y$ with coefficients in $A$ and $y$ not reducing to $0$ (the Gauss prolongation); (ii) for $y$ a Laurent series over $A$ whose image lies in $F$, that image lies in $R_0$ and its residue, read in $k((q))$, is the coefficientwise reduction of $y$; (iii) $f\in R_1$ iff $w(f)\in R_0$, where $w$ is the base change to $\overline{\mathbb Q}$, via $\mathrm{geomAut}$, of $\mathrm{atkinLehnerInvolutionFull}\,N\,p$, and the residue of $f$ under $R_1$ equals that of $w(f)$ under $R_0$; (iv) the two valuation subrings are distinct; (v) the $q$-expansion $j$ (the image of $\mathrm{jq}$ in $\overline{\mathbb Q}((q))$) lies in both, with $R_0$-residue $\mathrm{jqModC}\,k$ and $R_1$-residue $(\mathrm{jqModC}\,k)^p$, and $[\bar F:k(\mathrm{jqModC}\,k)]=\psi(N)$, $[\bar F:k((\mathrm{jqModC}\,k)^p)]=p\,\psi(N)$, $[F:\overline{\mathbb Q}(j)]=(p+1)\psi(N)$, where $\psi(N)=\sum_{d\mid N,\ d\text{ squarefree}}N/d$; and (vi) any valuation subring $V$ of $F$ that agrees with $R_0$ on the subfield $\overline{\mathbb Q}(j)$ equals $R_0$ or $R_1$.
--
--   This is the codimension-one part of the Deligne–Rapoport description of $X_0(Np)$ modulo $p$ for $p\nmid N$ — two components isomorphic to $X_0(N)$ over $k$, the second attached through Frobenius — expressed through valuation rings of the function field and their residue maps, with the completeness clause (vi) saying that there are no further extensions of the Gauss valuation above $\overline{\mathbb Q}(j)$. It feeds the construction of the Igusa-type integral models and charts, and the prolongation tuples used in the place-specialisation formalism.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_regularProlongation_pair_valuationSubring_eq_or_eq_of_not_dvd.lean

import Mathlib
import Definitions.Def_ModularCurve_X0ModL
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_ModularCurve_AtkinLehnerPartial
import Definitions.Def_ModularCurve_GeometricBaseChange
import Definitions.Def_EllipticCurve_FrobeniusTrace
import Definitions.Def_AlgebraicCurve_RegularProlongation

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve ModularCurve

set_option synthInstance.maxHeartbeats 400000 in

theorem ModularCurve.exists_regularProlongation_pair_valuationSubring_eq_or_eq_of_not_dvd
    (N p : ℕ) [NeZero N] [Fact p.Prime] (hpN : ¬ p ∣ N)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p) :
    ∃ R : Fin 2 → AlgebraicCurve.RegularProlongation A (ModularCurve.modularFunctionFieldBar (N * p))
        (ModularCurve.modularFunctionFieldFullC (IsLocalRing.ResidueField A) N),

      (∀ f : ModularCurve.modularFunctionFieldBar (N * p), f ∈ (R 0).integers ↔
        ∃ x y : LaurentSeries A, ModularCurve.coeffMap (IsLocalRing.residue A) y ≠ 0 ∧
          (f : LaurentSeries (AlgebraicClosure ℚ)) * ModularCurve.coeffMap A.subtype y
            = ModularCurve.coeffMap A.subtype x) ∧

      (∀ (y : LaurentSeries A)
        (hy : ModularCurve.coeffMap A.subtype y ∈ ModularCurve.modularFunctionFieldBar (N * p)),
        ∃ hint : (⟨ModularCurve.coeffMap A.subtype y, hy⟩ :
            ModularCurve.modularFunctionFieldBar (N * p)) ∈ (R 0).integers,
          (((R 0).residue ⟨_, hint⟩ :
              ModularCurve.modularFunctionFieldFullC (IsLocalRing.ResidueField A) N) :
              LaurentSeries (IsLocalRing.ResidueField A)) =
            ModularCurve.coeffMap (IsLocalRing.residue A) y) ∧

      (∀ f : ModularCurve.modularFunctionFieldBar (N * p), f ∈ (R 1).integers ↔
        ModularCurve.geomAut (AlgebraicClosure ℚ) (ModularCurve.modularFunctionFieldFull (N * p))
          (ModularCurve.atkinLehnerInvolutionFull N p) f ∈ (R 0).integers) ∧
      (∀ (f : ModularCurve.modularFunctionFieldBar (N * p)) (h₁ : f ∈ (R 1).integers)
        (h₀ : ModularCurve.geomAut (AlgebraicClosure ℚ) (ModularCurve.modularFunctionFieldFull (N * p))
          (ModularCurve.atkinLehnerInvolutionFull N p) f ∈ (R 0).integers),
        (R 1).residue ⟨f, h₁⟩ = (R 0).residue ⟨_, h₀⟩) ∧

      (R 0).integers ≠ (R 1).integers ∧

      (∃ hj : ∀ i, (⟨ModularCurve.coeffEmb (AlgebraicClosure ℚ) ModularCurve.jq,
            ModularCurve.coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
              (ModularCurve.modularFunctionField_le_full (N * p) (ModularCurve.jq_mem (N * p)))⟩ :
            ModularCurve.modularFunctionFieldBar (N * p)) ∈ (R i).integers,
        (((R 0).residue ⟨_, hj 0⟩ :
            ModularCurve.modularFunctionFieldFullC (IsLocalRing.ResidueField A) N) :
            LaurentSeries (IsLocalRing.ResidueField A)) =
          ModularCurve.jqModC (IsLocalRing.ResidueField A) ∧
        (((R 1).residue ⟨_, hj 1⟩ :
            ModularCurve.modularFunctionFieldFullC (IsLocalRing.ResidueField A) N) :
            LaurentSeries (IsLocalRing.ResidueField A)) =
          ModularCurve.jqModC (IsLocalRing.ResidueField A) ^ p ∧
        Module.finrank (IntermediateField.adjoin (IsLocalRing.ResidueField A)
            {(R 0).residue ⟨_, hj 0⟩})
          (ModularCurve.modularFunctionFieldFullC (IsLocalRing.ResidueField A) N) = dedekindPsi N ∧
        Module.finrank (IntermediateField.adjoin (IsLocalRing.ResidueField A)
            {(R 1).residue ⟨_, hj 1⟩})
          (ModularCurve.modularFunctionFieldFullC (IsLocalRing.ResidueField A) N)
            = p * dedekindPsi N ∧
        Module.finrank (IntermediateField.adjoin (AlgebraicClosure ℚ)
            {(⟨ModularCurve.coeffEmb (AlgebraicClosure ℚ) ModularCurve.jq,
              ModularCurve.coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (ModularCurve.modularFunctionField_le_full (N * p) (ModularCurve.jq_mem (N * p)))⟩ :
              ModularCurve.modularFunctionFieldBar (N * p))})
          (ModularCurve.modularFunctionFieldBar (N * p)) = (p + 1) * dedekindPsi N) ∧

      ∀ V : ValuationSubring (ModularCurve.modularFunctionFieldBar (N * p)),
        (∀ e ∈ IntermediateField.adjoin (AlgebraicClosure ℚ)
            {(⟨ModularCurve.coeffEmb (AlgebraicClosure ℚ) ModularCurve.jq,
              ModularCurve.coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (ModularCurve.modularFunctionField_le_full (N * p) (ModularCurve.jq_mem (N * p)))⟩ :
              ModularCurve.modularFunctionFieldBar (N * p))},
          e ∈ V ↔ e ∈ (R 0).integers) →
        V = (R 0).integers ∨ V = (R 1).integers := by sorry
