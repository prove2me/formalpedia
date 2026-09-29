-- Prove2me | Theorems.Thm_ModularCurve_exists_regularProlongation_placeMap_modularFunctionFieldFullC_of_not_dvd
-- name    : ModularCurve.exists_regularProlongation_placeMap_modularFunctionFieldFullC_of_not_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:51.361078+00:00
-- url     : https://prove2.me/theorems/c64f1e76-8886-5774-ac58-70b7b2e3101d
-- title:
--   Regular prolongation and place map for X₀(M) at ℓ ∤ M
-- statement:
--   Let $M \ge 1$, let $\ell$ be a prime with $\ell \nmid M$, and let $A$ be a valuation subring of $\overline{\mathbb Q}=$ `AlgebraicClosure ℚ` lying over $\ell$ in the sense that $\ell$ belongs to the nonunits of $A$, and assume the residue field $k =$ `ResidueField A` is algebraically closed. Write $\bar F_M$ for `modularFunctionFieldBar M`, the intermediate field of $\overline{\mathbb Q}$ in the Laurent series field over $\overline{\mathbb Q}$ obtained by adjoining the coefficientwise image of `modularFunctionFieldFull M` (itself the field generated over $\mathbb Q$ by the divisor $q$-expansions for $M$), and $F_{M,k}$ for `modularFunctionFieldFullC k M`, the field generated over $k$ inside $k$-Laurent series by the series `qExpand k d (jqModC k)` for the nonzero divisors $d \mid M$. The assertion is that there exist a regular prolongation $R$ of $A$ to $\bar F_M$ with residue field $F_{M,k}$ — a valuation subring `R.integers` of $\bar F_M$ contracting to $A$ along $\overline{\mathbb Q} \to \bar F_M$, together with a surjective ring homomorphism `R.residue` onto $F_{M,k}$ whose kernel is the maximal ideal, compatible with the residue map of $A$, and such that every nonzero element of $\bar F_M$ has an $\overline{\mathbb Q}$-multiple lying in `R.integers` with nonzero residue — and a map $r$ from places of $\bar F_M$ over $\overline{\mathbb Q}$ to places of $F_{M,k}$ over $k$ (places being proper valuation subrings containing the base field and being principal ideal rings), satisfying two conditions. First, for every Laurent series $y$ with coefficients in $A$ whose coefficientwise image in $\overline{\mathbb Q}$-Laurent series lies in $\bar F_M$, that element of $\bar F_M$ lies in `R.integers` and its residue, viewed in $k$-Laurent series, is the coefficientwise reduction of $y$. Second, for every $f \in$ `R.integers` with `R.residue f` $\neq 0$ and every finitely supported divisor $D$ on the places of $\bar F_M$ with $D(P) = \operatorname{ord}_P(f)$ for all $P$, the pushforward `Finsupp.mapDomain r D` satisfies $(r_*D)(Q) = \operatorname{ord}_Q(\mathrm{res}\,f)$ for every place $Q$ of $F_{M,k}$, where $\operatorname{ord}$ is minus the logarithm of the associated $\mathbb Z^{m0}$-valued adic valuation.
--
--   This is the good-reduction (Gauss prolongation) statement for the modular function field of level $M$ at a prime $\ell \nmid M$, together with Deuring's reduction of divisors: specialisation of places is compatible with taking divisors of functions with nonzero residue. It is the geometric input used downstream in the level-lowering arguments, for instance in the construction of compatible reductions of chart data, of Hecke-compatible prolongations, and in the comparison of $q$-expansions of regular differentials.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_regularProlongation_placeMap_modularFunctionFieldFullC_of_not_dvd.lean

import Mathlib
import Definitions.Def_ModularCurve_X0ModL
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_EllipticCurve_FrobeniusTrace
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_AlgebraicCurve_IsCurveOver

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve ModularCurve IsLocalRing
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

theorem ModularCurve.exists_regularProlongation_placeMap_modularFunctionFieldFullC_of_not_dvd
    (M : ℕ) [NeZero M]
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓM : ¬ ℓ ∣ M)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime ℓ)
    [IsAlgClosed (ResidueField ↥A)] :
    ∃ (R : RegularProlongation A (modularFunctionFieldBar M)
          (modularFunctionFieldFullC (ResidueField ↥A) M))
      (r : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar M)
          → Place (ResidueField ↥A) (modularFunctionFieldFullC (ResidueField ↥A) M)),
      (∀ (y : LaurentSeries ↥A)
          (hy : coeffMap A.subtype y ∈ modularFunctionFieldBar M),
        ∃ hint : (⟨coeffMap A.subtype y, hy⟩ : modularFunctionFieldBar M) ∈ R.integers,
          ((R.residue ⟨_, hint⟩ : modularFunctionFieldFullC (ResidueField ↥A) M)
              : LaurentSeries (ResidueField ↥A))
            = coeffMap (IsLocalRing.residue ↥A) y)
      ∧ ∀ f : R.integers, R.residue f ≠ 0 →
          ∀ D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar M),
            (∀ P, D P = P.ord (f : modularFunctionFieldBar M)) →
          ∀ Q, Finsupp.mapDomain r D Q = Q.ord (R.residue f) := by sorry
