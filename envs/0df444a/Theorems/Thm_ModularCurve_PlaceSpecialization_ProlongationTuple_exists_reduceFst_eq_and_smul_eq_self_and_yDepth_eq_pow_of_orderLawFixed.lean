-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_reduceFst_eq_and_smul_eq_self_and_yDepth_eq_pow_of_orderLawFixed
-- name    : ModularCurve.PlaceSpecialization.ProlongationTuple.exists_reduceFst_eq_and_smul_eq_self_and_yDepth_eq_pow_of_orderLawFixed
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:45.66333+00:00
-- url     : https://prove2.me/theorems/9bd3f0d2-39a3-505d-bd97-f371d5ea99b3
-- title:
--   Inertia-invariant places at prescribed depth over a supersingular node
-- statement:
--   Fix a prime $q$, a valuation subring $A$ of $\overline{\mathbb{Q}}$, a nonzero level $N$, a field $k$ of characteristic $q$ which is algebraically closed, a ring homomorphism $red : A \to k$, modular polynomial data `data` for $q$ satisfying the Kronecker congruence `hKr`, integrality of the two degeneracy embeddings $\bar\alpha,\bar\beta$ of $\overline{\mathbb{Q}}$-level-$N$ into level-$Nq$ modular function fields, and a `PlaceSpecialization` $P$ for these data. Let $R$ be a `ProlongationTuple` for $P$, assume $q \nmid N$, that $R$ satisfies `IsModel` (the two divisor laws and the two cusp laws) and the order law `OrderLawFixed` at the places fixed by the square of the geometric Frobenius, let $W$ be a finite set of places of `modularFunctionFieldC k N` each supersingular in the sense of `ssPlaces q N k`, and assume the regularity law and node value law of $R$ for $W$. Let $K \subset \overline{\mathbb{Q}}$ be finite over $\mathbb{Q}$, let $w \in W$ satisfy the value-integrality law `ValueIntegralityLaw`, let $\varpi \in A \cap K$, let $c$ be a node-coordinate datum for $R$ over $K$ at $w$, and let $c.x \cdot c.y = (\mathrm{nodeConst}_K^w\varpi)^E u$ with $u$ a unit of the node integer ring `nodeIntegersOver K w` and $E$ a natural number. Finally let $d > 0$ with $v_A(\varpi)^E < v_A(q)^d$ in the value group of $A$. Then there is a place $V$ of `modularFunctionFieldBar (N * q)` over $\overline{\mathbb{Q}}$ with `P.reduceFst V = w`, invariant under the arithmetic Galois action of every $\sigma$ in the inertia subgroup `A.inertiaSubgroupIn ℚ`, and with $c.\mathrm{yDepth}(V) = v_A(V(c.y)) = v_A(q)^d$.
--
--   This supplies the inertia-invariant points of the annulus lying over a supersingular crossing point of the modular curve of level $Nq$ in characteristic $q$: for every admissible depth strictly inside the annulus there is a place above the node, fixed by inertia, at exactly that depth. It is used in the construction of the annulus data at level $Nq$ and in the assembly of the place-specialization package with its depth and degree laws.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_reduceFst_eq_and_smul_eq_self_and_yDepth_eq_pow_of_orderLawFixed.lean

import Definitions.Def_ModularCurve_NodeDepth

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve
open ModularCurve.PlaceSpecialization ModularCurve.PlaceSpecialization.ProlongationTuple

theorem ModularCurve.PlaceSpecialization.ProlongationTuple.exists_reduceFst_eq_and_smul_eq_self_and_yDepth_eq_pow_of_orderLawFixed
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
    (w : Place k (modularFunctionFieldC k N)) (hw : w ∈ W)
    (hvalA : R.ValueIntegralityLaw w)
    (ϖ : ↥(NodeLocalized.coeffSubring A K))
    (c : R.NodeCoordinates K w) (E : ℕ) (u : ↥(R.nodeIntegersOver K w)) (hu : IsUnit u)
    (hxy : c.x * c.y = R.nodeConst K w ϖ ^ E * u)
    (d : ℕ) (hd : 0 < d)
    (hdE : A.valuation (ϖ : AlgebraicClosure ℚ) ^ E < A.valuation ((q : ℕ) : AlgebraicClosure ℚ) ^ d) :
    ∃ V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)), P.reduceFst V = w ∧
      (∀ σ ∈ A.inertiaSubgroupIn ℚ, arithmeticGalois (modularFunctionFieldFull (N * q)) σ • V = V) ∧
      c.yDepth V = A.valuation ((q : ℕ) : AlgebraicClosure ℚ) ^ d := by sorry
