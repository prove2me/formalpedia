-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_xDepth_pow_eq_valuation_pow_of_reduceFst_eq
-- name    : ModularCurve.PlaceSpecialization.ProlongationTuple.exists_xDepth_pow_eq_valuation_pow_of_reduceFst_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:45.66333+00:00
-- url     : https://prove2.me/theorems/91e5151d-d0d8-528d-8f42-bd4b8d7607d7
-- title:
--   Rational depth window for places over a supersingular node
-- statement:
--   Fix a prime $q$, a valuation subring $A$ of $\overline{\mathbb Q}$, a positive integer $N$, a field $k$ of characteristic $q$ and a ring homomorphism $\mathrm{red} : A \to k$; let $\mathrm{data}$ be modular polynomial data for $q$ (a monic $\Phi \in \mathbb Z[X][Y]$ of degree $\psi(q)$ killing the pair of $q$-expansions) together with the Kronecker congruence $\Phi \equiv (X^q - Y)(X - Y^q) \bmod q$, let $h\alpha$, $h\beta$ be the integrality hypotheses for the two degeneracy embeddings $\overline{F}_N \to \overline{F}_{Nq}$, and let $P$ be a place specialisation of this data and $R$ a prolongation tuple for $P$. Assume $k$ perfect, let $K$ be a finite extension of $\mathbb Q$ inside $\overline{\mathbb Q}$, let $w$ be a place of $\mathrm{modularFunctionFieldC}\ k\ N$, and let $B := R.\mathrm{nodeIntegersOver}\ K\ w$ be the ring of functions on $X_0(Nq)_{\overline{\mathbb Q}}$ integral for both prolongations and for all places above $w$ and defined over $K$. Let $c$ be node coordinates $(x,y)$ in $B$ (with $x$ reducing to $0$ for the first prolongation and of order $1$ at the Frobenius twist of $w$ for the second, and symmetrically for $y$), and $\varpi \in A \cap K$. Assume $B$ local and Noetherian, with maximal ideal spanned by the constant $\varpi$ together with $x$ and $y$; assume every $g \in B$ differs from some constant from $A \cap K$ by a non-unit; assume the value-integrality law at $w$, namely $V.\mathrm{evalAt}\,f \in A$ for every $f$ integral at $w$ and every place $V$ with $P.\mathrm{reduceFst}\,V = w$; and assume $w$ is a supersingular place (rational, affine geometric, with $j$-value in the supersingular $j$-set for $q$). Let $W$ be a complete discrete valuation domain, adically complete for its maximal ideal, $\pi \in W$ irreducible, $E \ge 1$, and let $\iota$ be a ring isomorphism from the $\mathfrak m_B$-adic completion of $B$ onto the crossing model $\mathrm{MvPowerSeries}(\{0,1\}, W)/(X_0X_1 - \pi^E)$ carrying the image of the constant $\varpi$ to the constant $\pi$ and the image of $x$ to $U \cdot \alpha_U$ with $\alpha_U$ a unit, $U$ the class of the first variable. Then for every place $V$ of $\mathrm{modularFunctionFieldBar}(Nq)$ over $\overline{\mathbb Q}$ with $P.\mathrm{reduceFst}\,V = w$ there are integers $r \ge 1$ and $p \ge 1$ with $p + 1 \le rE$ and $$c.\mathrm{xDepth}\,V^{\,r} = A.\mathrm{valuation}(\varpi)^{\,p}$$ in the value group of $A$, where $c.\mathrm{xDepth}\,V = A.\mathrm{valuation}(V.\mathrm{evalAt}\,x)$.
--
--   In the crossing presentation $W[[U,V]]/(UV-\pi^E)$ of the completed local ring at a supersingular node of $X_0(Nq)$, this says that each place of the geometric function field reducing to the node has $x$-depth commensurable with the depth of the chosen uniformiser $\varpi$, with ratio $p/r$ lying strictly between $0$ and $E$: every such place sits on a circle of rational depth inside the open annulus. It is used in the computation of $\sum \mathrm{ord}$ as a sum of ranks times lengths, where the depths of the places above the node are grouped and matched with the model side.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_xDepth_pow_eq_valuation_pow_of_reduceFst_eq.lean

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

theorem ModularCurve.PlaceSpecialization.ProlongationTuple.exists_xDepth_pow_eq_valuation_pow_of_reduceFst_eq
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
    (αU : UVCrossingModel W (π ^ E)) (hαU : IsUnit αU) (hιx : ι (algebraMap _ _ c.x) = U (π ^ E) * αU) :
    ∀ V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)), P.reduceFst V = w →
      ∃ r : ℕ, 1 ≤ r ∧ ∃ p : ℕ, 1 ≤ p ∧ p + 1 ≤ r * E ∧
        c.xDepth V ^ r = A.valuation ((ϖ : ↥(NodeLocalized.coeffSubring A K)) : AlgebraicClosure ℚ) ^ p := by sorry
