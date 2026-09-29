-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_sum_ord_le_finsum_rank_mul_length_of_ringEquiv_uvCrossingModel
-- name    : ModularCurve.PlaceSpecialization.ProlongationTuple.sum_ord_le_finsum_rank_mul_length_of_ringEquiv_uvCrossingModel
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:45.66333+00:00
-- url     : https://prove2.me/theorems/4227e82b-b78a-577a-93ea-20c306fd9c42
-- title:
--   Places over a supersingular node bounded by horizontal primes
-- statement:
--   Fix a prime $q$, a valuation subring $A$ of $\overline{\mathbb Q}$, a nonzero level $N$, a perfect field $k$ of characteristic $q$, a ring homomorphism $\mathrm{red} : A \to k$, modular polynomial data `data` for $q$ satisfying the Kronecker congruence `hKr`, integrality hypotheses `hα`, `hβ` for the two degeneracy maps $\overline{\mathbb Q}$-base-changed from level $N$ to level $Nq$, a place specialization $P$ built from these, and a prolongation tuple $R$ for $P$. Let $K \subset \overline{\mathbb Q}$ be a finite extension of $\mathbb Q$, let $w$ be a place of $\mathrm{modularFunctionFieldC}\ k\ N$, let $c$ be a choice of node coordinates $x, y$ for $R$ over $K$ at $w$, and let $\varpi$ lie in the coefficient subring $A \cap K$. Write $B := R.\mathrm{nodeIntegersOver}\ K\ w$, the subring of functions at level $Nq$ that are integral for $R_1$, for $R_2$ and at all places above $w$, and whose Laurent expansions lie in the field generated over $K$-coefficients. Assume $B$ is local and Noetherian with maximal ideal spanned by the image of $\varpi$ together with $x$ and $y$; that every $g \in B$ differs from the image of some $o \in A \cap K$ by a non-unit; that the value-integrality law holds at $w$, i.e. $V.\mathrm{evalAt}\,f \in A$ for every $f$ in the node integers and every place $V$ with $P.\mathrm{reduceFst}\,V = w$; and that $w$ is supersingular (rational, affine geometric, with $j$-value in the supersingular set for $q$). Let $W$ be a complete discrete valuation domain with irreducible element $\pi$, let $E \ge 1$, and let $\iota$ be a ring isomorphism from the adic completion of $B$ at its maximal ideal onto the crossing model $\mathcal R := W[[U,V]]/(UV - \pi^{E})$ carrying the image of $\varpi$ to the constant $\pi$ and the image of $x$ to $U \alpha$ for a unit $\alpha$. Let $f \in B$ be nonzero, let $r \ge 1$ and $p \ge 1$ with $p + 1 \le rE$, and let $T$ be the finite set of places $V$ of the level-$Nq$ function field over $\overline{\mathbb Q}$ with $\mathrm{ord}_V f \ne 0$, $P.\mathrm{reduceFst}\,V = w$ and $(v_A(V.\mathrm{evalAt}\,x))^{r} = (v_A(\varpi))^{p}$. Then, in $\mathbb N^\infty$, the sum over $V \in T$ of $(\mathrm{ord}_V f)$, truncated to $\mathbb N$, is at most the finite sum, over those primes $Q$ of $\mathcal R$ with $Q \ne 0$, $\pi \notin Q$ and $r \cdot \mathrm{length}_W(\mathcal R/(Q + U\mathcal R)) = p \cdot \mathrm{rank}_W(\mathcal R/Q)$, of $\mathrm{rank}_W(\mathcal R/Q)$ times the length, over the localization of $\mathcal R$ at $Q$, of the localization of $\mathcal R/(\iota(f))$ at $Q$.
--
--   This is the inequality half of the count of places of the level-$Nq$ modular function field lying above a supersingular node and having prescribed depth $p/r$ in the $x$-coordinate: each such place contributes to a horizontal prime of the crossing model $W[[U,V]]/(UV-\pi^{E})$ of the completed node ring, with multiplicity bounded by the local length there and with at most $\mathrm{rank}_W(\mathcal R/Q)$ places per prime. It is used by [`ModularCurve.PlaceSpecialization.ProlongationTuple.sum_ord_eq_finsum_rank_mul_length_of_total_eq`](thm.html#ModularCurve.PlaceSpecialization.ProlongationTuple.sum_ord_eq_finsum_rank_mul_length_of_total_eq), where the reverse comparison upgrades it to an equality.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_sum_ord_le_finsum_rank_mul_length_of_ringEquiv_uvCrossingModel.lean

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

theorem ModularCurve.PlaceSpecialization.ProlongationTuple.sum_ord_le_finsum_rank_mul_length_of_ringEquiv_uvCrossingModel
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
    (r : ℕ) (hr : 1 ≤ r) (p : ℕ) (hp1 : 1 ≤ p) (hpE : p + 1 ≤ r * E)
    (T : Finset (Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))))
    (hT : ∀ V, V ∈ T ↔ (V.ord ((f : ↥(modularFunctionFieldBar (N * q)))) ≠ 0 ∧ P.reduceFst V = w ∧
        c.xDepth V ^ r = A.valuation ((ϖ : ↥(NodeLocalized.coeffSubring A K)) : AlgebraicClosure ℚ) ^ p)) :
    ((∑ V ∈ T, (V.ord ((f : ↥(modularFunctionFieldBar (N * q))))).toNat : ℕ) : ℕ∞) ≤
      ∑ᶠ (Q : PrimeSpectrum (UVCrossingModel W (π ^ E)))
        (_ : Q.asIdeal ≠ ⊥ ∧ const (π ^ E) π ∉ Q.asIdeal ∧
          (r : ℕ∞) * Module.length W (UVCrossingModel W (π ^ E) ⧸ (Q.asIdeal ⊔ Ideal.span {U (π ^ E)})) =
            ((p * Module.finrank W (UVCrossingModel W (π ^ E) ⧸ Q.asIdeal) : ℕ) : ℕ∞)),
        (Module.finrank W (UVCrossingModel W (π ^ E) ⧸ Q.asIdeal) : ℕ∞) *
          Module.length (Localization.AtPrime Q.asIdeal)
            (LocalizedModule Q.asIdeal.primeCompl
              (UVCrossingModel W (π ^ E) ⧸ Ideal.span {ι (algebraMap _ _ f)})) := by sorry
