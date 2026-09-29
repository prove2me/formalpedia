-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_isLocalRing_and_isNoetherianRing_nodeIntegersOver_of_nodeCoordinates_of_orderLawFixed_of_range_redRestrict
-- name    : ModularCurve.PlaceSpecialization.ProlongationTuple.isLocalRing_and_isNoetherianRing_nodeIntegersOver_of_nodeCoordinates_of_orderLawFixed_of_range_redRestrict
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:45.66333+00:00
-- url     : https://prove2.me/theorems/43be41f2-9f7c-59b8-b1d7-1f95c9cea593
-- title:
--   Node ring over K at supersingular place is local noetherian
-- statement:
--   Fix a prime $q$, a valuation subring $A$ of $\overline{\mathbb Q}$, a nonzero level $N$, a field $k$ of characteristic $q$ and a ring homomorphism $\mathrm{red} : A \to k$; fix modular polynomial data `data` for $q$ (a monic bivariate integral polynomial of degree $\psi(q)$ annihilating the pair $(j, j_q)$) together with a proof `hKr` of the Kronecker congruence $\Phi \equiv (X^q - Y)(X - Y^q)$ modulo $q$, and integrality hypotheses $h\alpha$, $h\beta$ for the Hecke $\bar\alpha$- and $\bar\beta$-maps at level $N$ and prime $q$; let $P$ be a place specialisation of this data and $R : \mathrm{ProlongationTuple}\ P$ a prolongation tuple over it, with $k$ algebraically closed. Assume $q \nmid N$; that $R$ satisfies `IsModel` (the two divisor laws and the two cusp laws), the fixed order law `OrderLawFixed`, and, for a finite set $W$ of places of $\mathrm{modularFunctionFieldC}\ k\ N$ all of which are supersingular (lie in $\mathrm{ssPlaces}\ q\ N\ k$), the laws $\mathrm{RegularityLaw}\ W$ and $\mathrm{NodeValueLaw}\ W$. Let $K$ be a finite extension of $\mathbb Q$ inside $\overline{\mathbb Q}$ such that every $a \in k$ with $a^{q^2} = a$ lies in the image of $\mathrm{NodeLocalized.redRestrict}\ \mathrm{red}\ K$, i.e. is the reduction of an element of the coefficient subring $A \cap K$. Let $w \in W$, and suppose given node coordinates $c : R.\mathrm{NodeCoordinates}\ K\ w$, that is a pair $x, y$ in $R.\mathrm{nodeIntegersOver}\ K\ w$ with $\mathrm{nodeResidue}_1(x) = 0$, $\mathrm{ord}_{\varphi w}(\mathrm{nodeResidue}_2(x)) = 1$ for $\varphi$ the arithmetic Frobenius translation, $\mathrm{nodeResidue}_2(y) = 0$ and $\mathrm{ord}_w(\mathrm{nodeResidue}_1(y)) = 1$. Then the ring $R.\mathrm{nodeIntegersOver}\ K\ w$ — the subring of those $f$ in $\mathrm{modularFunctionFieldBar}\ (N q)$ lying in $R.\mathrm{nodeIntegers}\ w$ whose underlying Laurent series lies in $\mathrm{NodeLocalized.fieldOver}\ (Nq)\ K$ — is a local ring and is noetherian.
--
--   The assertion is that the ring of functions on $X_0(Nq)$ with coefficients over $K$ which are integral at the supersingular node attached to the pair $(w, \varphi w)$ is a noetherian local ring; it is the variant of the corresponding unconditional statement in which the fixed order law is assumed and, in addition, the residue field of $A \cap K$ is required to contain $\mathbb F_{q^2}$. It feeds the construction of node packages and of inertia-fixed presentations of node coordinates over $K$, and the uniqueness statement for the place of the first prolongation at which the coordinate $y$ takes a prescribed value.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_isLocalRing_and_isNoetherianRing_nodeIntegersOver_of_nodeCoordinates_of_orderLawFixed_of_range_redRestrict.lean

import Definitions.Def_ModularCurve_NodeLocalizedPlaces

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve
open ModularCurve.PlaceSpecialization
open ModularCurve.PlaceSpecialization.ProlongationTuple

theorem
ModularCurve.PlaceSpecialization.ProlongationTuple.isLocalRing_and_isNoetherianRing_nodeIntegersOver_of_nodeCoordinates_of_orderLawFixed_of_range_redRestrict
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    {P : PlaceSpecialization A q N data hKr k red hα hβ}
    (R : ProlongationTuple P) [IsAlgClosed k] [DecidableEq k] (hqN : ¬ q ∣ N)
    (hmodel : R.IsModel) (hO : R.OrderLawFixed)
    (W : Finset (Place k (modularFunctionFieldC k N))) (hW : ∀ w ∈ W, w ∈ ssPlaces q N k)
    (hreg : R.RegularityLaw W) (hval : R.NodeValueLaw W)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    (hk₀ : ∀ a : k, a ^ (q ^ 2) = a → a ∈ Set.range (NodeLocalized.redRestrict red K))
    (w : Place k (modularFunctionFieldC k N)) (hw : w ∈ W) (c : R.NodeCoordinates K w) :
    IsLocalRing ↥(R.nodeIntegersOver K w) ∧ IsNoetherianRing ↥(R.nodeIntegersOver K w) := by sorry
