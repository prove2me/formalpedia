-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_exists_ord_sub_pow_sq_eq_one_of_mem_ssPlaces
-- name    : ModularCurve.PlaceSpecialization.exists_ord_sub_pow_sq_eq_one_of_mem_ssPlaces
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.056571+00:00
-- url     : https://prove2.me/theorems/8c393c9e-2f90-560c-b874-f568131513da
-- title:
--   Lifting a uniformiser at a supersingular place, with pole control
-- statement:
--   Fix a prime $q$, a valuation subring $A$ of $\overline{\mathbb{Q}}$, a nonzero level $N$, a field $k$ of characteristic $q$ and a ring homomorphism $red : A \to k$; fix modular polynomial data `data` for $q$ (a monic $\Phi \in \mathbb{Z}[X][Y]$ of degree $\psi(q)$ annihilating the pair $(j, j_q)$) together with a proof `hKr` that its reduction modulo $q$ equals $(C X^q - X)(C X - X^q)$, and proofs $h\alpha$, $h\beta$ that the two Hecke homomorphisms $\bar\alpha$, $\bar\beta$ at level $N$ and prime $q$ over $\overline{\mathbb{Q}}$ are integral. Let $P$ be a place specialisation datum for these data, let $k$ be algebraically closed with decidable equality, assume $q \nmid N$, and let $w$ be a place of $\mathrm{modularFunctionFieldC}\,k\,N$, the subfield of $k$-Laurent series generated over $k$ by the reductions of the $q$-expansions of $j$ and $j_N$, with $w$ supersingular in the sense of `ssPlaces q N k`. Then there exist a Laurent series $g_0$ over $\mathbb{Q}$ lying in $\mathrm{modularFunctionFieldFull}\,N$, a Laurent series $y$ with coefficients in $A$, an element $g$ of the base change $\mathrm{modularFunctionFieldBar}\,N$ of that field to $\overline{\mathbb{Q}}$, and an element $\bar g$ of $\mathrm{modularFunctionFieldC}\,k\,N$, such that $g$ is the coefficientwise image of $g_0$ under $\mathbb{Q} \to \overline{\mathbb{Q}}$, the coefficientwise image of $y$ under $A \hookrightarrow \overline{\mathbb{Q}}$ is that same series, $\bar g$ is the coefficientwise image of $y$ under $red$, the order of $\bar g - \bar g^{q^2}$ equals $1$ both at $w$ and at the translate of $w$ by the coefficientwise semilinear automorphism $\mathrm{arithFrobC}\,q\,k\,N$ induced by the Frobenius of $k$, and finally $g$ lies in the valuation subring of every place $U$ of $\mathrm{modularFunctionFieldBar}\,N$ over $\overline{\mathbb{Q}}$ whose specialisation $P.\mathrm{sp}\,U$ either equals $w$, or maps to $w$ under $\mathrm{frobOnPlacesGeomLevel}$, or equals the image of $w$ under $\mathrm{frobOnPlacesGeomLevel}$.
--
--   This provides, at a supersingular place of the characteristic-$q$ fibre of the level-$N$ modular curve, a function defined over $\mathbb{Q}$ with $A$-integral $q$-expansion whose reduction has $\bar g - \bar g^{q^2}$ vanishing to order exactly one at $w$ and at its arithmetic Frobenius translate, while no pole of the characteristic-zero function $g$ lies over $w$, over a geometric Frobenius preimage of $w$, or over the Frobenius image of $w$. It is used in the analysis of the nodes of the special fibre at level $Nq$, in particular in the statements about node packs, node coordinates and the completion of the node integers at a crossing model.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_exists_ord_sub_pow_sq_eq_one_of_mem_ssPlaces.lean

import Definitions.Def_ModularCurve_NodeLocalizedPlaces

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve
open ModularCurve.PlaceSpecialization ModularCurve.PlaceSpecialization.ProlongationTuple

theorem ModularCurve.PlaceSpecialization.exists_ord_sub_pow_sq_eq_one_of_mem_ssPlaces
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    (P : PlaceSpecialization A q N data hKr k red hα hβ) [IsAlgClosed k] [DecidableEq k] (hqN : ¬ q ∣ N)
    (w : Place k (modularFunctionFieldC k N)) (hw : w ∈ ssPlaces q N k) :
    ∃ (g₀ : LaurentSeries ℚ) (y : LaurentSeries ↥A) (g : ↥(modularFunctionFieldBar N))
      (gbar : ↥(modularFunctionFieldC k N)),
      g₀ ∈ modularFunctionFieldFull N ∧
      (g : LaurentSeries (AlgebraicClosure ℚ)) = coeffEmb (AlgebraicClosure ℚ) g₀ ∧
      coeffMap A.subtype y = coeffEmb (AlgebraicClosure ℚ) g₀ ∧
      (gbar : LaurentSeries k) = coeffMap red y ∧
      w.ord (gbar - gbar ^ (q ^ 2)) = 1 ∧ (arithFrobC q k N • w).ord (gbar - gbar ^ (q ^ 2)) = 1 ∧
      ∀ U : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N),
        (P.sp U = w ∨ frobOnPlacesGeomLevel k N data hKr (P.sp U) = w ∨
            P.sp U = frobOnPlacesGeomLevel k N data hKr w) →
          g ∈ U.toValuationSubring := by sorry
