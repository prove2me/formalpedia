-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_exists_ringHom_fieldBar_comap_gauss_iff_of_isAlgebraic
-- name    : ModularCurve.FullLevel.exists_ringHom_fieldBar_comap_gauss_iff_of_isAlgebraic
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:35.562543+00:00
-- url     : https://prove2.me/theorems/e44dbbe0-f799-5c10-aad1-99ee5747740f
-- title:
--   Transport of the Gauss valuation ring along an embedding of constants
-- statement:
--   Let $q\ge 5$ be a prime and $M'$ a positive integer not divisible by $q$, and write $H=$ `levelH q M'` for the kernel of the reduction map $(\mathbf{Z}/q^2M')^\times\to(\mathbf{Z}/q)^\times$. Let $L$ be a field of characteristic zero, algebraic over $\mathbf{Q}$, let $\zeta\in L$ be a primitive $q$-th root of unity, and assume there is a ring homomorphism $L\to\mathbf{C}$ carrying $\zeta$ to $\exp(2\pi i/q)$. Let $K$ be the intermediate field of $L\subseteq L((X))$ obtained by adjoining to $L$ the coefficientwise image of the function field `xHFunctionField (q ^ 2 * M') H` $\subseteq\mathbf{Q}((X))$ under $\mathbf{Q}\to L$. Let $A$ be a discrete valuation ring with fraction field $L$ such that $q$ lies in the maximal ideal of $A$ and $\zeta$ lies in the image of $A$, and let $W_0$ be a valuation subring of $K$ consisting exactly of those $f$ for which there are power series $x,y$ over $A$ with $y$ of nonzero reduction modulo the maximal ideal and $f\cdot y=x$ in $L((X))$ after applying $A\to L$ coefficientwise. Then there exist a ring homomorphism $e\colon L\to\overline{\mathbf{Q}}$, a valuation subring $A'$ of $\overline{\mathbf{Q}}$ in which $q$ is a nonunit, a primitive $q$-th root of unity $\zeta'$ in $\overline{\mathbf{Q}}$, a ring homomorphism $\iota_K\colon K\to$ `fieldBar q M'` (the corresponding intermediate field of $\overline{\mathbf{Q}}\subseteq\overline{\mathbf{Q}}((X))$) and a valuation subring $O$ of `fieldBar q M'` such that $\zeta'=e(\zeta)$; $\iota_K$ acts on underlying Laurent series by applying $e$ to coefficients; $O$ consists exactly of those $f$ for which there are Laurent series $x,y$ over $A'$ with $y$ of nonzero coefficientwise residue and $f\cdot y=x$ in $\overline{\mathbf{Q}}((X))$; and $W_0$ is the preimage of $O$ under $\iota_K$.
--
--   This transports the Gauss valuation ring on the function field of the level structure over an arbitrary algebraic constant field $L$ to the corresponding Gauss ring over $\overline{\mathbf{Q}}$, so that questions about it may be settled over $\overline{\mathbf{Q}}$ alone. It is used in the analysis of the behaviour of the $\infty$-branch of the Igusa curve under level automorphisms, in particular by the results comparing a Gauss valuation ring with its conjugates and by the construction of $q$-expansions separating these rings.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_exists_ringHom_fieldBar_comap_gauss_iff_of_isAlgebraic.lean

import Mathlib
import Definitions.Def_ModularCurve_XH
import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_FLTPrelim_Ramification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsLocalRing

theorem ModularCurve.FullLevel.exists_ringHom_fieldBar_comap_gauss_iff_of_isAlgebraic
    (q : ℕ) [Fact q.Prime] (hq : 5 ≤ q) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (L : Type) [Field L] [CharZero L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ q)
    (hι : ∃ ι : L →+* ℂ, ι ζ = Complex.exp (2 * Real.pi * Complex.I / q))
    [Algebra.IsAlgebraic ℚ L]
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L
      (ModularCurve.xHFunctionField (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M')))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAq : (q : A) ∈ IsLocalRing.maximalIdeal A) (hζA : ∃ x : A, algebraMap A L x = ζ)
    (W₀ : ValuationSubring ↥K)
    (hW₀ : ∀ f : ↥K, f ∈ W₀ ↔ ∃ x y : PowerSeries A, y.map (IsLocalRing.residue A) ≠ 0 ∧
      (f : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap A L))
        = HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L))) :
    ∃ (e : L →+* AlgebraicClosure ℚ)
      (A' : ValuationSubring (AlgebraicClosure ℚ)) (_ : A'.LiesOverPrime q)
      (ζ' : ModularCurve.FullLevel.Idx q)
      (ιK : ↥K →+* ↥(ModularCurve.FullLevel.fieldBar q M'))
      (O : ValuationSubring ↥(ModularCurve.FullLevel.fieldBar q M')),
      ζ'.val = e ζ ∧
      (∀ x : ↥K, ((ιK x : ↥(ModularCurve.FullLevel.fieldBar q M')) : LaurentSeries (AlgebraicClosure ℚ)) =
        ModularCurve.coeffMap e (x : LaurentSeries L)) ∧
      (∀ f : ↥(ModularCurve.FullLevel.fieldBar q M'), f ∈ O ↔
        ∃ x y : LaurentSeries ↥A', ModularCurve.coeffMap (IsLocalRing.residue ↥A') y ≠ 0 ∧
          (f : LaurentSeries (AlgebraicClosure ℚ)) * ModularCurve.coeffMap A'.subtype y = ModularCurve.coeffMap A'.subtype x) ∧
      (∀ f : ↥K, ιK f ∈ O ↔ f ∈ W₀) := by sorry
