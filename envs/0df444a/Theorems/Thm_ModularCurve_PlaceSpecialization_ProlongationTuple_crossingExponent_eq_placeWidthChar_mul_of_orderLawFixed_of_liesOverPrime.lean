-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_crossingExponent_eq_placeWidthChar_mul_of_orderLawFixed_of_liesOverPrime
-- name    : ModularCurve.PlaceSpecialization.ProlongationTuple.crossingExponent_eq_placeWidthChar_mul_of_orderLawFixed_of_liesOverPrime
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:44.572352+00:00
-- url     : https://prove2.me/theorems/eea42d53-5e93-57e1-bbb1-f12b5bb86674
-- title:
--   Node crossing exponent equals characteristic-q width times e_K
-- statement:
--   Let $q$ be a prime and $A$ a valuation subring of $\overline{\mathbb{Q}}$ lying over $q$, meaning that $q$ is a nonunit of $A$; write $k = \kappa(A)$ for its residue field, assumed of characteristic $q$ and algebraically closed, and take the reduction map to be the residue map $A \to k$. Let $N \ge 1$ with $q \nmid N$, let `data` be modular polynomial data for $q$ (a monic $\Phi$ of degree $\psi(q)$ in the second variable annihilating the pair of $q$-expansions) satisfying the Kronecker congruence $\Phi \equiv (Y^q - X)(Y - X^q) \bmod q$, and let $h\alpha$, $h\beta$ assert integrality of the two degeneracy embeddings of the level-$N$ into the level-$Nq$ Laurent function field. Let $P$ be a place specialisation of level $N$ at $A$ with residue data as above and $R$ a prolongation tuple over $P$, consisting of two regular prolongations $R_1$, $R_2$ of $A$ in the level-$Nq$ field together with the compatibilities recorded in `ProlongationTuple`. Assume $R$ is a model, i.e. it satisfies the two divisor laws and the two cusp laws, and let $W$ be a finite set of places of `modularFunctionFieldC k N`, each rational, affine for the two $j$-generators, and with supersingular $j$-invariant; assume further the regularity law and the node value law for $W$, and the fixed-point order law. Let $K \subset \overline{\mathbb{Q}}$ be a number field, $w \in W$, and $\varpi \in A \cap K$ an element whose multiples are exactly the elements of $A \cap K$ killed by the reduction map, with $q = \varpi^{e_K}\varepsilon$ for a unit $\varepsilon$ of $A \cap K$. Finally let $c$ be a node-coordinate datum at $w$ over $K$, that is a pair $x, y$ in the node ring `R.nodeIntegersOver K w` with first residue of $x$ zero, second residue of $x$ of order $1$ at the arithmetic-Frobenius translate of $w$, second residue of $y$ zero and first residue of $y$ of order $1$ at $w$, and suppose $x y = (\varpi \cdot 1)^{E} u$ for some $E \in \mathbb{N}$ and some unit $u$ of that node ring, $\varpi$ being mapped into the node ring by `R.nodeConst K w`. Then $E = \mathrm{placeWidthChar}(q,N,w) \cdot e_K$, where the width is the characteristic-$q$ corrected width of the $j$-value of $w$ divided by the ramification index of $j$ at $w$.
--
--   This identifies the exponent in the local equation $xy = \varpi^{E}$ of a supersingular crossing point on the reduction of $X_0(Nq)$ with the product of the characteristic-$q$ width of the corresponding point of the $j$-line and the absolute ramification $e_K$ of the coefficient field. It is the form of the crossing-exponent computation with no hypothesis that the supersingular $j$-invariant of $w$ be the reduction of an element of $A \cap K$ — such a lift need not exist, for instance for $K = \mathbb{Q}(\zeta_q)$ — and it feeds the construction of the local rings at supersingular points in the two-chart integral model of $X_0(Nq)$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_crossingExponent_eq_placeWidthChar_mul_of_orderLawFixed_of_liesOverPrime.lean

import Definitions.Def_ModularCurve_NodeLocalizedPlaces
import Definitions.Def_ModularCurve_PlaceWidthChar

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
open AlgebraicCurve IsLocalRing ModularCurve
open ModularCurve.PlaceSpecialization
open ModularCurve.PlaceSpecialization.ProlongationTuple

theorem ModularCurve.PlaceSpecialization.ProlongationTuple.crossingExponent_eq_placeWidthChar_mul_of_orderLawFixed_of_liesOverPrime
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} (hA : A.LiesOverPrime q) {N : ℕ} [NeZero N]
    [CharP (IsLocalRing.ResidueField ↥A) q]
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    {P : PlaceSpecialization A q N data hKr (IsLocalRing.ResidueField ↥A) (IsLocalRing.residue ↥A) hα hβ}
    (R : ProlongationTuple P) [IsAlgClosed (IsLocalRing.ResidueField ↥A)] [DecidableEq (IsLocalRing.ResidueField ↥A)]
    (hqN : ¬ q ∣ N) (hmodel : R.IsModel)
    (W : Finset (Place (IsLocalRing.ResidueField ↥A) (modularFunctionFieldC (IsLocalRing.ResidueField ↥A) N)))
    (hW : ∀ w ∈ W, w ∈ ssPlaces q N (IsLocalRing.ResidueField ↥A))
    (hreg : R.RegularityLaw W) (hval : R.NodeValueLaw W) (hord : R.OrderLawFixed)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    (w : Place (IsLocalRing.ResidueField ↥A) (modularFunctionFieldC (IsLocalRing.ResidueField ↥A) N)) (hw : w ∈ W)
    (ϖ : ↥(NodeLocalized.coeffSubring A K))
    (hϖ : ∀ d : ↥(NodeLocalized.coeffSubring A K),
      NodeLocalized.redRestrict (IsLocalRing.residue ↥A) K d = 0 ↔ ∃ d', d = ϖ * d')
    (eK : ℕ) (ε : ↥(NodeLocalized.coeffSubring A K)) (hε : IsUnit ε)
    (hqe : ((q : ℕ) : ↥(NodeLocalized.coeffSubring A K)) = ϖ ^ eK * ε)
    (c : R.NodeCoordinates K w) (E : ℕ) (u : ↥(R.nodeIntegersOver K w)) (hu : IsUnit u)
    (hxy : c.x * c.y = R.nodeConst K w ϖ ^ E * u) :
    E = placeWidthChar q N w * eK := by sorry
