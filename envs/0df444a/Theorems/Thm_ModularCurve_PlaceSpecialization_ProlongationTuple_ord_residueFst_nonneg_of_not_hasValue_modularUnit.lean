-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_ord_residueFst_nonneg_of_not_hasValue_modularUnit
-- name    : ModularCurve.PlaceSpecialization.ProlongationTuple.ord_residueFst_nonneg_of_not_hasValue_modularUnit
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:45.66333+00:00
-- url     : https://prove2.me/theorems/62f475d1-851f-5150-a088-30ea950cd018
-- title:
--   First residue regular at an ordinary fixed place, Atkin–Lehner case
-- statement:
--   Fix $N\ge 1$ and a prime $q$ with $q\nmid N$, a valuation subring $A$ of $\overline{\mathbb{Q}}$, an algebraically closed field $k$ of characteristic $q$ and a ring homomorphism $red : A\to k$, together with a `ModularPolynomialData` $data$ for $q$ satisfying the Kronecker congruence $hKr$ and integrality hypotheses $h\alpha$, $h\beta$ for the two degeneracy embeddings `heckeAlphaBar`, `heckeBetaBar` of the geometric level-$N$ function field into the geometric level-$Nq$ function field $\mathrm{modularFunctionFieldBar}(Nq)$, the latter assumed to have principal divisors; let $P$ be a `PlaceSpecialization` for these data and $R$ a `ProlongationTuple` over $P$, consisting of two regular prolongations $R_1,R_2$ of $A$ to the level-$Nq$ field with residues into the level-$N$ field over the residue field of $A$, together with their Atkin–Lehner compatibility. Assume $R$ satisfies the four model laws `DivisorLawFst`, `DivisorLawSnd`, `CuspLawInfty`, `CuspLawZero`, and the law `OrderLawFixed` relating, at a $\varphi^2$-fixed affine place, the pushforward under `reduceFst` of the divisor of a doubly integral function to the sum of the orders of its two residues. Let $u$ be an element of the level-$Nq$ field whose Laurent expansion is the coefficientwise image of `modularUnitSeries` $q$, namely $\Delta$ divided by its $q$-fold expansion. Let $g$ lie in the valuation subrings of both $R_1$ and $R_2$ with $R_1$-residue non-zero, and let $V_0$ be a place of the level-$Nq$ field such that: the Frobenius action `frobOnPlacesGeomLevel` squared fixes $v := P.\mathrm{reduceFst}\,V_0$; both $j$ and $j_N$ lie in the valuation subring of $v$ (affineness); $v$ is not supersingular, i.e. not in `ssPlaces` $q$ $N$ $k$; every place $W\ne V_0$ with $P.\mathrm{reduceFst}\,W = v$ satisfies $\operatorname{ord}_W g\ge 0$; and there is no $a\in A$ with $red\,a\ne 0$ such that $u$ lies in the valuation subring of $V_0$ with residue the image of $a$. Then $\operatorname{ord}_v$ of the first residue $R.\mathrm{residue}_1\langle g,h_1\rangle$ is non-negative.
--
--   This is the second half of the local regularity statement for the first residue of a doubly integral function on the level-$Nq$ curve at an ordinary affine place fixed by the square of Frobenius, treating the case where the modular unit $u$ does not take a unit value at $V_0$, so that $V_0$ lies on the zero sheet. It feeds the computation of the pushforward of the divisor restricted to the first sheet as the order of the first residue, used in the reduction of $X_0(Nq)$ modulo $q$ underlying level lowering.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_ord_residueFst_nonneg_of_not_hasValue_modularUnit.lean

import Mathlib
import Definitions.Def_ModularCurve_ProlongationTuple
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_ModularCurve_ModularUnit
import Definitions.Def_ModularCurve_CuspidalClass

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option Elab.async false
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

open AlgebraicCurve ModularCurve ModularCurve.PlaceSpecialization

theorem ModularCurve.PlaceSpecialization.ProlongationTuple.ord_residueFst_nonneg_of_not_hasValue_modularUnit
    {N : ℕ} [NeZero N] {q : ℕ} [Fact q.Prime] (hqN : ¬ q ∣ N)
    {A : ValuationSubring (AlgebraicClosure ℚ)} {k : Type*} [Field k]
    [CharP k q] [DecidableEq k] [IsAlgClosed k]
    [HasPrincipalDivisors (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))]
    {red : A →+* k} {data : ModularPolynomialData q}
    {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    (P : PlaceSpecialization A q N data hKr k red hα hβ)
    (R : ProlongationTuple P) (hR : R.IsModel) (hO : R.OrderLawFixed)
    (u : modularFunctionFieldBar (N * q))
    (hu : (u : LaurentSeries (AlgebraicClosure ℚ))
      = coeffEmb (AlgebraicClosure ℚ) (modularUnitSeries q))
    (g : modularFunctionFieldBar (N * q)) (h₁ : g ∈ R.R₁.integers) (h₂ : g ∈ R.R₂.integers)
    (hres₁ : R.R₁.residue ⟨g, h₁⟩ ≠ 0)
    (V₀ : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)))
    (hfix : frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr (P.reduceFst V₀))
      = P.reduceFst V₀)
    (haff : IsAffineGeomPlace k N (P.reduceFst V₀))
    (hord : P.reduceFst V₀ ∉ ssPlaces q N k)
    (hpole : ∀ W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)),
      P.reduceFst W = P.reduceFst V₀ → W ≠ V₀ → 0 ≤ W.ord g)
    (hV₀ : ¬ ∃ a : A, red a ≠ 0 ∧ V₀.HasValue u (a : AlgebraicClosure ℚ)) :
    0 ≤ (P.reduceFst V₀).ord (R.residue₁ ⟨g, h₁⟩) := by sorry
