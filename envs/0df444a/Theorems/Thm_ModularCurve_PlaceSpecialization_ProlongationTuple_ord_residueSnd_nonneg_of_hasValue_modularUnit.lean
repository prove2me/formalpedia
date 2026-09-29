-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_ord_residueSnd_nonneg_of_hasValue_modularUnit
-- name    : ModularCurve.PlaceSpecialization.ProlongationTuple.ord_residueSnd_nonneg_of_hasValue_modularUnit
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:45.66333+00:00
-- url     : https://prove2.me/theorems/feb90186-e6d8-5b4e-aed8-287c97756ce3
-- title:
--   Regularity of the second residue at φ v via a modular unit
-- statement:
--   Fix $N \ge 1$ and a prime $q$ with $q \nmid N$, a valuation subring $A$ of $\overline{\mathbb Q}$, an algebraically closed field $k$ of characteristic $q$ and a ring homomorphism $\mathrm{red} : A \to k$; fix modular polynomial data `data` for $q$ satisfying the Kronecker congruence `hKr`, i.e. the reduction of $\Phi$ modulo $q$ is $(Y^q - X)(Y - X^q)$, and hypotheses `hα`, `hβ` that the two degeneracy maps $\overline{\mathbb Q}$-algebra maps from level $N$ to level $Nq$ (inclusion, and substitution $q \mapsto q^{q}$) are integral; assume every nonzero element of `modularFunctionFieldBar (N * q)` has a degree-zero divisor recording its orders. Let $P$ be a place specialization datum and $R$ a prolongation tuple over $P$ satisfying the four model laws `R.IsModel` (the two divisor laws and the two cusp laws) and the order law at fixed places `R.OrderLawFixed`. Let $u$ be an element of `modularFunctionFieldBar (N * q)` whose Laurent series is the coefficientwise image of the modular unit $\Delta(q)\,\Delta(q^{q})^{-1}$, and let $g$ lie in the integers of both $R.R_1$ and $R.R_2$ with $R.R_2$-residue nonzero. Let $V_0$ be a place of `modularFunctionFieldBar (N * q)` such that $v =$ `P.reduceFst V₀` is fixed by applying `frobOnPlacesGeomLevel k N data hKr` twice, satisfies `IsAffineGeomPlace k N v` (both generators $j$ and $j_N$ of the level-$N$ function field over $k$ lie in its valuation subring), and such that every place $W \ne V_0$ with `P.reduceFst W = v` satisfies $0 \le W.\mathrm{ord}\, g$. Assume finally that there is $a \in A$ with $\mathrm{red}\, a \ne 0$ and $V_0.$`HasValue` $u\ a$, i.e. $u$ lies in the valuation subring of $V_0$ and its residue is the image of $a$. Then $0 \le$ the order of `R.residue₂ ⟨g, h₂⟩` at `frobOnPlacesGeomLevel k N data hKr v`.
--
--   This is the level-$N$ case, for $q \nmid N$, of the local regularity statement used when computing the reduction of functions on $X_0(Nq)$ in characteristic $q$: the value of the modular unit $\Delta(q)/\Delta(q^{q})$ at $V_0$ being a $q$-adic unit identifies $V_0$ as lying on the sheet through the cusp $\infty$, and the order law at affine $\varphi^2$-fixed places then forces the second residue to have no pole at $\varphi v$. It feeds the two lemmas that evaluate the pushforward along `P.reduceFst` of the first-sheet part of a divisor as the order of the first residue.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_ord_residueSnd_nonneg_of_hasValue_modularUnit.lean

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

theorem ModularCurve.PlaceSpecialization.ProlongationTuple.ord_residueSnd_nonneg_of_hasValue_modularUnit
    {N : ℕ} [NeZero N] {q : ℕ} [Fact q.Prime] (hqN : ¬ q ∣ N)
    {A : ValuationSubring (AlgebraicClosure ℚ)} {k : Type*} [Field k]
    [CharP k q] [IsAlgClosed k]
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
    (hres₂ : R.R₂.residue ⟨g, h₂⟩ ≠ 0)
    (V₀ : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)))
    (hfix : frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr (P.reduceFst V₀))
      = P.reduceFst V₀)
    (haff : IsAffineGeomPlace k N (P.reduceFst V₀))
    (hpole : ∀ W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)),
      P.reduceFst W = P.reduceFst V₀ → W ≠ V₀ → 0 ≤ W.ord g)
    (a : A) (ha : red a ≠ 0) (hV₀ : V₀.HasValue u (a : AlgebraicClosure ℚ)) :
    0 ≤ (frobOnPlacesGeomLevel k N data hKr (P.reduceFst V₀)).ord (R.residue₂ ⟨g, h₂⟩) := by sorry
