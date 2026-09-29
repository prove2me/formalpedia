-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_card_le_finsum_finrank_quotient_map_of_forall_mem_iff_evalAt_eq_zero
-- name    : ModularCurve.PlaceSpecialization.ProlongationTuple.card_le_finsum_finrank_quotient_map_of_forall_mem_iff_evalAt_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:44.572352+00:00
-- url     : https://prove2.me/theorems/4a647a70-ae5c-585e-8c85-9b64d68241b6
-- title:
--   Places over a supersingular node bounded by total branch rank
-- statement:
--   Fix a prime $q$, a valuation subring $A$ of $\overline{\mathbb Q}$, a level $N \neq 0$, a field $k$ of characteristic $q$ with a ring map $\mathrm{red} : A \to k$, modular polynomial data for $q$ satisfying the Kronecker congruence, integrality of the two Hecke degeneracy embeddings, and a place specialisation $P$; let $R$ be a prolongation tuple for $P$, with $k$ perfect. Let $K/\mathbb Q$ be a finite intermediate field of $\overline{\mathbb Q}$, $w$ a place of $\mathrm{modularFunctionFieldC}\ k\ N$, and $c$ a system of node coordinates $x,y$ in $B := R.\mathrm{nodeIntegersOver}\ K\ w$ (the functions in $\mathrm{modularFunctionFieldBar}(Nq)$ integral for $R_1$, for $R_2$ and at every place $V$ of $\overline{\mathbb Q}$ with $P.\mathrm{reduceFst}\ V = w$, whose Laurent expansion lies in $\mathrm{fieldOver}(Nq)\ K$). Let $\varpi \neq 0$ in $A \cap K$. Assume: $B$ is local and Noetherian with maximal ideal spanned by the constant $\varpi$ together with $c.x$ and $c.y$; every $g \in B$ differs from some constant by a non-unit; the value integrality law for $w$ (for $f \in R.\mathrm{nodeIntegers}\ w$ and $V$ over $w$, $V.\mathrm{evalAt}\ f \in A$); and $w$ is a supersingular place. Let $W$ be a complete discrete valuation domain with irreducible $\pi$, $E \geq 1$, and $\iota$ a ring isomorphism from the adic completion $\widehat B$ onto the crossing model $W[[X_0,X_1]]/(X_0X_1 - \pi^E)$ carrying the constant $\varpi$ to the class of $\pi$ and $c.x$ to $X_0$ times a unit; assume $A \cap K$ is a discrete valuation ring with maximal ideal $(\varpi)$, and that some ring isomorphism $\tau$ from its adic completion onto $W$ sends $\varpi$ to $\pi$ and matches $\iota$ on constants. Let $\mathfrak q$ be an ideal of $B$ whose image $J$ under $B \to \widehat B \xrightarrow{\iota}$ the crossing model has finite $W$-module quotient, and let $S$ be a finite set of places $V$ of $\mathrm{modularFunctionFieldBar}(Nq)$ over $\overline{\mathbb Q}$ such that each $V$ satisfies $P.\mathrm{reduceFst}\ V = w$ and $g \in \mathfrak q \iff V.\mathrm{evalAt}\ g = 0$ for all $g \in B$, and such that distinct members of $S$ differ at some $g \in B$. Then $\#S$, as an element of $\mathbb N_\infty$, is at most the finite sum over those points $Q$ of the prime spectrum of the crossing model that are minimal over $J$ and do not contain the class of $\pi$, of $\mathrm{finrank}_W$ of the crossing model modulo $Q$.
--
--   This is the depth-free counting step in the local analysis of $X_0(Nq)$ at a supersingular point: places of the function field lying over the node and sharing a prescribed evaluation kernel are bounded in number by the total $W$-rank of the branches of the completed local ring $W[[X_0,X_1]]/(X_0X_1-\pi^E)$ cut out by that kernel, away from the special fibre. It is obtained from the general bound on algebra homomorphisms out of a module-finite algebra over a discrete valuation ring, and feeds the summation over nodes in [`ModularCurve.PlaceSpecialization.ProlongationTuple.sum_toNat_ord_le_length_mul_finsum_finrank_of_forall_mem_iff_evalAt_eq_zero`](thm.html#ModularCurve.PlaceSpecialization.ProlongationTuple.sum_toNat_ord_le_length_mul_finsum_finrank_of_forall_mem_iff_evalAt_eq_zero).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_card_le_finsum_finrank_quotient_map_of_forall_mem_iff_evalAt_eq_zero.lean

import Mathlib
import Definitions.Def_ModularCurve_NodeDepth
import Definitions.Def_ModularCurve_UVCrossingModel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.PlaceSpecialization Valued
open ModularCurve.UVCrossingModel Valued in

theorem ModularCurve.PlaceSpecialization.ProlongationTuple.card_le_finsum_finrank_quotient_map_of_forall_mem_iff_evalAt_eq_zero
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    {P : PlaceSpecialization A q N data hKr k red hα hβ}
    (R : ProlongationTuple P) [PerfectField k]
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    (w : Place k (modularFunctionFieldC k N)) (c : R.NodeCoordinates K w)
    (ϖ : ↥(NodeLocalized.coeffSubring A K)) (hϖ0 : ϖ ≠ 0)
    [IsLocalRing ↥(R.nodeIntegersOver K w)] [IsNoetherianRing ↥(R.nodeIntegersOver K w)]
    (hmax : IsLocalRing.maximalIdeal ↥(R.nodeIntegersOver K w) = Ideal.span {R.nodeConst K w ϖ, c.x, c.y})
    (hres : ∀ g : ↥(R.nodeIntegersOver K w), ∃ o : ↥(NodeLocalized.coeffSubring A K), ¬ IsUnit (g - R.nodeConst K w o))
    (hVI : R.ValueIntegralityLaw w) [DecidableEq k] (hwss : w ∈ ssPlaces q N k)
    {W : Type u} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [IsAdicComplete (IsLocalRing.maximalIdeal W) W]
    (π : W) (hπ : Irreducible π) (E : ℕ) (hE : 1 ≤ E)
    (ι : AdicCompletion (IsLocalRing.maximalIdeal ↥(R.nodeIntegersOver K w)) ↥(R.nodeIntegersOver K w)
          ≃+* UVCrossingModel W (π ^ E))
    (hιϖ : ι (algebraMap _ _ (R.nodeConst K w ϖ)) = const (π ^ E) π)
    (αU : UVCrossingModel W (π ^ E)) (hαU : IsUnit αU) (hιx : ι (algebraMap _ _ c.x) = U (π ^ E) * αU)
    [IsDiscreteValuationRing ↥(NodeLocalized.coeffSubring A K)]
    (hϖgen : IsLocalRing.maximalIdeal ↥(NodeLocalized.coeffSubring A K) = Ideal.span {ϖ})
    (hτ : ∃ τ : AdicCompletion (IsLocalRing.maximalIdeal ↥(NodeLocalized.coeffSubring A K))
        ↥(NodeLocalized.coeffSubring A K) ≃+* W,
      (∀ o : ↥(NodeLocalized.coeffSubring A K),
        ι (algebraMap _ _ (R.nodeConst K w o)) = const (π ^ E) (τ (algebraMap _ _ o))) ∧
      τ (algebraMap _ _ ϖ) = π)
    (𝔮 : Ideal ↥(R.nodeIntegersOver K w))
    (hJfin : Module.Finite W (UVCrossingModel W (π ^ E) ⧸ Ideal.map (ι.toRingHom.comp (algebraMap ↥(R.nodeIntegersOver K w) (AdicCompletion (IsLocalRing.maximalIdeal ↥(R.nodeIntegersOver K w)) ↥(R.nodeIntegersOver K w)))) 𝔮))
    (S : Finset (Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))))
    (hS : ∀ V ∈ S, P.reduceFst V = w ∧
      (∀ g : ↥(R.nodeIntegersOver K w), g ∈ 𝔮 ↔ V.evalAt ((g : ↥(modularFunctionFieldBar (N * q)))) = 0))
    (hsep : ∀ V ∈ S, ∀ V' ∈ S,
      (∀ g : ↥(R.nodeIntegersOver K w), V.evalAt ((g : ↥(modularFunctionFieldBar (N * q))))
        = V'.evalAt ((g : ↥(modularFunctionFieldBar (N * q))))) → V = V') :
    (S.card : ℕ∞) ≤
      ∑ᶠ (Q : PrimeSpectrum (UVCrossingModel W (π ^ E)))
        (_ : Q.asIdeal ∈ (Ideal.map (ι.toRingHom.comp (algebraMap ↥(R.nodeIntegersOver K w) (AdicCompletion (IsLocalRing.maximalIdeal ↥(R.nodeIntegersOver K w)) ↥(R.nodeIntegersOver K w)))) 𝔮).minimalPrimes ∧ const (π ^ E) π ∉ Q.asIdeal),
        (Module.finrank W ((UVCrossingModel W (π ^ E)) ⧸ Q.asIdeal) : ℕ∞) := by sorry
