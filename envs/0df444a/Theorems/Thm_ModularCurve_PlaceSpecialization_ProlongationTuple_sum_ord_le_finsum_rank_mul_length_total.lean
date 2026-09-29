-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_sum_ord_le_finsum_rank_mul_length_total
-- name    : ModularCurve.PlaceSpecialization.ProlongationTuple.sum_ord_le_finsum_rank_mul_length_total
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:45.66333+00:00
-- url     : https://prove2.me/theorems/f5b474ee-8a97-5b02-8342-ffba31591839
-- title:
--   Total order over a node bounded by horizontal crossing-model count
-- statement:
--   Fix a prime $q$, a valuation subring $A$ of $\overline{\mathbb Q}$, a nonzero level $N$, a perfect field $k$ of characteristic $q$ and a ring homomorphism $red : A \to k$; fix modular polynomial data for $q$ satisfying the Kronecker congruence $\Phi \equiv (Y^{q}-X)(Y-X^{q})$ mod $q$, integrality hypotheses $h\alpha, h\beta$ for the two degeneracy maps $\overline{M}_N \to \overline{M}_{Nq}$, a place specialization $P$ of these data and a prolongation tuple $R$ for $P$. Let $K \subset \overline{\mathbb Q}$ be a finite extension of $\mathbb Q$, let $w$ be a place of $\mathrm{modularFunctionFieldC}\ k\ N$, let $c$ be a system of node coordinates $(x,y)$ for $R$ over $K$ at $w$, and let $\varpi$ lie in the coefficient ring $A \cap K$. Write $B := R.\mathrm{nodeIntegersOver}\ K\ w$, the subring of functions in $\mathrm{modularFunctionFieldBar}(Nq)$ integral for $R_1$, for $R_2$ and at every place $V$ with $P.\mathrm{reduceFst}\ V = w$, whose Laurent expansion lies in $\mathrm{fieldOver}(Nq)\ K$. Assume $B$ is local and Noetherian with maximal ideal $(\varpi, x, y)$ (the constant $\varpi$ being taken via $R.\mathrm{nodeConst}$), that every $g \in B$ differs from some constant $o \in A \cap K$ by a non-unit, that the value-integrality law holds at $w$ (each $f$ integral at $w$ has $V.\mathrm{evalAt}\ f \in A$ for all $V$ over $w$), and that $w$ is a supersingular place (rational, affine geometric, with $j$-value in $\mathrm{ssJSet}$). Let $W$ be a complete discrete valuation domain, $\pi$ irreducible in $W$, $E \ge 1$, and let $\iota$ be a ring isomorphism from the adic completion of $B$ at its maximal ideal onto the crossing model $W[[U,V]]/(UV - \pi^{E})$, carrying the image of $\varpi$ to the constant $\pi$ and the image of $x$ to $U \cdot \alpha_U$ with $\alpha_U$ a unit. Let $f \in B$ be nonzero and let $Ttot$ be the finite set of places $V$ of $\mathrm{modularFunctionFieldBar}(Nq)$ over $\overline{\mathbb Q}$ with $V.\mathrm{ord}\ f \ne 0$ and $P.\mathrm{reduceFst}\ V = w$. Then, in $\mathbb N_\infty$, $\sum_{V \in Ttot} (V.\mathrm{ord}\ f)_{\ge 0}$ is at most the (finitely supported) sum, over prime ideals $Q$ of the crossing model with $Q \ne 0$ and the constant $\pi \notin Q$, of $\operatorname{finrank}_W(\mathcal R/Q)$ times the length over $\mathcal R_Q$ of the localisation at $Q$ of $\mathcal R/(\iota(\hat f))$, where $\mathcal R$ denotes the crossing model.
--
--   This is the depth-free comparison between the total vanishing order of a function of the node ring at the places of the curve of level $Nq$ lying over a supersingular node and the horizontal intersection count of its divisor on the crossing model $W[[U,V]]/(UV-\pi^{E})$, each horizontal prime being weighted by its $W$-rank and by the local multiplicity of $\iota(\hat f)$. It feeds the bounds on the orders of the two residues of a node-ring element at $w$ and at its Frobenius translate.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_sum_ord_le_finsum_rank_mul_length_total.lean

import Mathlib
import Definitions.Def_ModularCurve_NodeDepth
import Definitions.Def_ModularCurve_UVCrossingModel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.PlaceSpecialization
open ModularCurve.UVCrossingModel in

theorem ModularCurve.PlaceSpecialization.ProlongationTuple.sum_ord_le_finsum_rank_mul_length_total
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    {P : PlaceSpecialization A q N data hKr k red hα hβ}
    (R : ProlongationTuple P) [PerfectField k]
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    (w : Place k (modularFunctionFieldC k N)) (c : R.NodeCoordinates K w)
    (ϖ : ↥(NodeLocalized.coeffSubring A K))
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
    (f : ↥(R.nodeIntegersOver K w)) (hf : f ≠ 0)
    (Ttot : Finset (Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))))
    (hTtot : ∀ V, V ∈ Ttot ↔ (V.ord ((f : ↥(modularFunctionFieldBar (N * q)))) ≠ 0 ∧ P.reduceFst V = w)) :
    ((∑ V ∈ Ttot, (V.ord ((f : ↥(modularFunctionFieldBar (N * q))))).toNat : ℕ) : ℕ∞) ≤
      ∑ᶠ (Q : PrimeSpectrum (UVCrossingModel W (π ^ E))) (_ : Q.asIdeal ≠ ⊥ ∧ const (π ^ E) π ∉ Q.asIdeal),
        (Module.finrank W (UVCrossingModel W (π ^ E) ⧸ Q.asIdeal) : ℕ∞) *
          Module.length (Localization.AtPrime Q.asIdeal)
            (LocalizedModule Q.asIdeal.primeCompl
              (UVCrossingModel W (π ^ E) ⧸ Ideal.span {ι (algebraMap _ _ f)})) := by sorry
