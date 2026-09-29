-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_glueData_mem_admissible_of_isGoodDiv_of_ord_eq_of_not_dvd
-- name    : ModularCurve.PlaceSpecialization.ProlongationTuple.glueData_mem_admissible_of_isGoodDiv_of_ord_eq_of_not_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:45.66333+00:00
-- url     : https://prove2.me/theorems/c83c1f61-c8b4-5a25-8634-7d6075bbf8bf
-- title:
--   Good principal divisors yield admissible gluing data
-- statement:
--   Fix a prime $q$, a valuation subring $A$ of $\overline{\mathbb{Q}}$, a nonzero natural number $N$ with $q \nmid N$, a perfect field $k$ of characteristic $q$ and a ring homomorphism $\mathrm{red} : A \to k$; let `data` be a modular polynomial datum for $q$, i.e. a monic $\Phi \in \mathbb{Z}[X][Y]$ of degree $\psi(q)$ annihilating the pair of $q$-expansions, subject to the Kronecker congruence $\Phi \equiv (X^{q} - Y)(X - Y^{q}) \bmod q$, let $h_\alpha, h_\beta$ assert that the two level-raising inclusions `heckeAlphaBar`, `heckeBetaBar` from level $N$ to level $Nq$ over $\overline{\mathbb{Q}}$ are integral, and let $P$ be a place specialization for these data, with its two reduction maps $r_1 =$ `P.reduceFst` and $r_2 =$ `P.reduceSnd` from places of `modularFunctionFieldBar (N * q)` to places of `modularFunctionFieldC k N`. Write $\varphi$ for `frobOnPlacesGeomLevel k N data hKr`. Let $W$ be a finite set of places of `modularFunctionFieldC k N` and $R$ a prolongation tuple for $P$ satisfying: the model laws `R.IsModel` (the two divisor laws, which off the $\varphi^2$-fixed locus compute the push-forwards of the strict parts of a principal divisor as the orders of the two residues, and the two cusp laws at $\infty$-side and $0$-side places), the regularity law `R.RegularityLaw W` and the order law `R.OrderLawFixed` at $\varphi^{2}$-fixed affine places. Assume further that both coordinates of every pair $s$ in `nodePairsOfPlaces (arithFrobC q k N) W` (the image of $W$ under the node-pair embedding attached to the coefficientwise Frobenius semilinear automorphism of `modularFunctionFieldC k N`) are fixed by $\varphi^{2}$. Let $f$ be an element of `modularFunctionFieldBar (N * q)` lying in the valuation subrings `R.R₁.integers` and `R.R₂.integers` whose two residues `R.residue₁ ⟨f, h₁⟩` and `R.residue₂ ⟨f, h₂⟩` are nonzero, and let $D$ be the divisor with $D(V) = \mathrm{ord}_V(f)$ for every place $V$, assumed good in the sense that every place in its support is either strict for the first or strict for the second reduction. Then the gluing datum `P.glueData` of $D$ at these node pairs, namely the triple consisting of the push-forward along $r_1$ of the strict-first part of $D$, the push-forward along $r_2$ of the strict-second part of $D$, and the trivial unit component, is admissible: both divisors have degree $0$, the first vanishes at $s.1$ and the second at $s.2$ for every node pair $s$.
--
--   This is the bidegree-$(0,0)$ and node-avoidance check for the gluing datum attached to the divisor of a function that is a unit for both Gauss prolongations, in the description of the special fibre at $q$ of the Jacobian of $X_0(Nq)$ as a Picard group of a glued curve. It is used in the construction of good admissible representatives of divisor classes avoiding a prescribed finite set of reductions.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_glueData_mem_admissible_of_isGoodDiv_of_ord_eq_of_not_dvd.lean

import Definitions.Def_ModularCurve_GlueData
import Definitions.Def_ModularCurve_ProlongationTuple

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

open AlgebraicCurve IsLocalRing

theorem ModularCurve.PlaceSpecialization.ProlongationTuple.glueData_mem_admissible_of_isGoodDiv_of_ord_eq_of_not_dvd
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N] (hqN : ¬ q ∣ N)
    {k : Type*} [Field k] [CharP k q] [PerfectField k] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    {P : PlaceSpecialization A q N data hKr k red hα hβ}
    (W : Finset (Place k (modularFunctionFieldC k N)))
    (R : P.ProlongationTuple) (hR : R.IsModel) (hNR : R.RegularityLaw W) (hO : R.OrderLawFixed)
    (hW : ∀ s ∈ nodePairsOfPlaces (arithFrobC q k N) W,
      frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr s.1) = s.1 ∧
      frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr s.2) = s.2)
    (f : modularFunctionFieldBar (N * q)) (h₁ : f ∈ R.R₁.integers) (h₂ : f ∈ R.R₂.integers)
    (hr₁ : R.residue₁ ⟨f, h₁⟩ ≠ 0) (hr₂ : R.residue₂ ⟨f, h₂⟩ ≠ 0)
    (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) (hD : ∀ V, D V = V.ord f)
    (hgood : P.IsGoodDiv D) :
    P.glueData (nodePairsOfPlaces (arithFrobC q k N) W) D ∈
      GluingData.admissible (nodePairsOfPlaces (arithFrobC q k N) W) := by sorry
