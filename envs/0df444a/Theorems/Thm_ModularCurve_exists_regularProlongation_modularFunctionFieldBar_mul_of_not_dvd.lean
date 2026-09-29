-- Prove2me | Theorems.Thm_ModularCurve_exists_regularProlongation_modularFunctionFieldBar_mul_of_not_dvd
-- name    : ModularCurve.exists_regularProlongation_modularFunctionFieldBar_mul_of_not_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:51.361078+00:00
-- url     : https://prove2.me/theorems/66a9d5f8-b1cf-5c0b-860b-b8d13e71444c
-- title:
--   Gauss prolongation of X₀(Nq) at a place above q∤ N
-- statement:
--   Let $N\ge 1$ and let $q$ be a prime with $q\nmid N$, and let $A$ be a valuation subring of $\overline{\mathbb Q}=$ `AlgebraicClosure ℚ` lying over $q$, meaning that $q$ is a non-unit of $A$; write $k=$ `IsLocalRing.ResidueField A` for its residue field. Put $F=$ [`ModularCurve.modularFunctionFieldBar (N * q)`](def/ModularCurve_ArithmeticGalois.html#L111), the subfield of $\overline{\mathbb Q}((\mathfrak q))$ generated over $\overline{\mathbb Q}$ by the coefficientwise images of the $\mathfrak q$-expansions $\mathrm{qExpand}\,d\,j$ for the divisors $d$ of $Nq$, and $\bar F=$ [`ModularCurve.modularFunctionFieldFullC k N`](def/ModularCurve_X0ModL.html#L100), the subfield of $k((\mathfrak q))$ generated over $k$ by $\mathrm{qExpand}\,d\,\bar\jmath$ for the nonzero divisors $d$ of $N$. The assertion is that there is a regular prolongation $R$ of $A$ to $F$ with residue field $\bar F$, i.e. a valuation subring $R.\mathrm{integers}$ of $F$ together with a surjective ring homomorphism $R.\mathrm{residue}$ onto $\bar F$ whose kernel is the maximal ideal, such that a constant $c\in\overline{\mathbb Q}$ lies in $R.\mathrm{integers}$ exactly when $c\in A$, the residue map restricted to constants is $A\to k\hookrightarrow\bar F$, and every nonzero $f\in F$ has a constant multiple lying in $R.\mathrm{integers}$ with nonzero residue; and moreover $R$ is the Gauss ring in two explicit senses: (i) $f\in F$ lies in $R.\mathrm{integers}$ if and only if $f\cdot y=x$ for some Laurent series $x,y$ with coefficients in $A$ whose reduction $y\bmod\mathfrak m_A$ is nonzero, these series being pushed into $\overline{\mathbb Q}((\mathfrak q))$ along $A\hookrightarrow\overline{\mathbb Q}$; and (ii) for every Laurent series $y$ over $A$ whose image in $\overline{\mathbb Q}((\mathfrak q))$ belongs to $F$, that element lies in $R.\mathrm{integers}$ and its residue, read inside $k((\mathfrak q))$, is the coefficientwise reduction of $y$.
--
--   This is the valuation-theoretic form, in the style of Deuring's reduction of function fields, of the description of the special fibre of $X_0(Nq)$ at a prime $q\nmid N$: the Gauss valuation at the cusp $\infty$ prolongs $A$ with residue field the level-$N$ modular function field over $k$, corresponding to the component of the fibre containing $\infty$. It underlies the construction of characteristic-$p$ models of modular function fields and the prolongation tuples used to specialise places in the analysis of $X_0(Nq)$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_regularProlongation_modularFunctionFieldBar_mul_of_not_dvd.lean

import Mathlib
import Definitions.Def_ModularCurve_X0ModL
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_EllipticCurve_FrobeniusTrace
import Definitions.Def_AlgebraicCurve_RegularProlongation

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve ModularCurve

set_option synthInstance.maxHeartbeats 400000 in

theorem ModularCurve.exists_regularProlongation_modularFunctionFieldBar_mul_of_not_dvd
    (N q : ℕ) [NeZero N] [Fact q.Prime] (hqN : ¬ q ∣ N)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q) :
    ∃ R : AlgebraicCurve.RegularProlongation A (ModularCurve.modularFunctionFieldBar (N * q))
        (ModularCurve.modularFunctionFieldFullC (IsLocalRing.ResidueField A) N),
      (∀ f : ModularCurve.modularFunctionFieldBar (N * q), f ∈ R.integers ↔
        ∃ x y : LaurentSeries A, ModularCurve.coeffMap (IsLocalRing.residue A) y ≠ 0 ∧
          (f : LaurentSeries (AlgebraicClosure ℚ)) * ModularCurve.coeffMap A.subtype y
            = ModularCurve.coeffMap A.subtype x) ∧
      ∀ (y : LaurentSeries A)
        (hy : ModularCurve.coeffMap A.subtype y ∈ ModularCurve.modularFunctionFieldBar (N * q)),
        ∃ hint : (⟨ModularCurve.coeffMap A.subtype y, hy⟩ : ModularCurve.modularFunctionFieldBar (N * q)) ∈
            R.integers,
          ((R.residue ⟨_, hint⟩ :
              ModularCurve.modularFunctionFieldFullC (IsLocalRing.ResidueField A) N) :
              LaurentSeries (IsLocalRing.ResidueField A)) =
            ModularCurve.coeffMap (IsLocalRing.residue A) y := by sorry
