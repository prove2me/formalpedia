-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_existsUnique_reduceFst_eq_and_hasValue_y_of_orderLawFixed
-- name    : ModularCurve.PlaceSpecialization.ProlongationTuple.existsUnique_reduceFst_eq_and_hasValue_y_of_orderLawFixed
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:44.572352+00:00
-- url     : https://prove2.me/theorems/0355d704-c319-53a1-bb65-1073e142f1d5
-- title:
--   Unique place over a supersingular node with prescribed value of y
-- statement:
--   Fix a prime $q$, a valuation subring $A$ of $\overline{\mathbb{Q}}$, an integer $N \ge 1$, a field $k$ of characteristic $q$, a ring homomorphism $\mathrm{red} : A \to k$, a modular polynomial datum `data` for $q$ satisfying the Kronecker congruence `hKr` (its reduction modulo $q$ is $(\mathrm{C}\,X^q - X)(\mathrm{C}\,X - X^q)$), integrality hypotheses `hα`, `hβ` for the two degeneracy embeddings of $\overline{\mathbb{Q}}$-level-$N$ into level-$Nq$ function fields, and a place specialisation $P$ of these data. Let $R$ be a prolongation tuple over $P$, with $k$ algebraically closed, and assume: $q \nmid N$; $R$ is a model (the two divisor laws and the two cusp laws) and satisfies the fixed-place order law `OrderLawFixed`; $W$ is a finite set of places of the geometric level-$N$ function field over $k$, all supersingular in the sense of `ssPlaces q N k`, for which $R$ satisfies the regularity law and the node-value law; $w \in W$; and $R$ satisfies the value-integrality law at $w$, i.e. every element of `R.nodeIntegers w` has value in $A$ at every place $V$ of the level-$Nq$ function field over $\overline{\mathbb{Q}}$ with $P.\mathrm{reduceFst}\,V = w$. Let $K_0 \subseteq \overline{\mathbb{Q}}$ be a finite extension of $\mathbb{Q}$ fixed pointwise by the inertia subgroup of $A$ over $\mathbb{Q}$, such that an element $d$ of $A \cap K_0$ has $\mathrm{redRestrict}(d) = 0$ exactly when $d$ is a multiple of $q$ in $A \cap K_0$. Let $c_1 = (x, y)$ be a datum of node coordinates of $R$ over $K_0$ at $w$, let $E_0 \in \mathbb{N}$ and let $u_0$ be a unit of `R.nodeIntegersOver K₀ w` with $x\,y = \mathrm{nodeConst}(q)^{E_0} u_0$. Finally let $c \in A$ lie in the maximal ideal of $A$ and admit $m$ in the maximal ideal with $c\,m = q^{E_0}$. Then there is exactly one place $V$ of the level-$Nq$ function field over $\overline{\mathbb{Q}}$ with $P.\mathrm{reduceFst}\,V = w$ at which $y$ has value $c$, that is, $y$ lies in the valuation subring of $V$ and its residue is the image of $c$ in the residue field of $V$.
--
--   This is the parametrisation of the points of the level-$Nq$ curve lying over a supersingular crossing point of the special fibre by the interior values of one branch coordinate: with the local relation $xy = q^{E_0}\cdot(\text{unit})$ in force, each $c$ in the maximal ideal of $A$ admitting a complementary factor $m$ with $cm = q^{E_0}$ is attained by a single place above $w$. It feeds the computation of the depth of $y$ together with Galois-equivariance of the resulting place.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_existsUnique_reduceFst_eq_and_hasValue_y_of_orderLawFixed.lean

import Definitions.Def_ModularCurve_NodeDepth

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve
open ModularCurve.PlaceSpecialization ModularCurve.PlaceSpecialization.ProlongationTuple

section
variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
  {k : Type*} [Field k] [CharP k q] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
  {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
  {P : PlaceSpecialization A q N data hKr k red hα hβ}

theorem ModularCurve.PlaceSpecialization.ProlongationTuple.existsUnique_reduceFst_eq_and_hasValue_y_of_orderLawFixed
    (R : ProlongationTuple P) [IsAlgClosed k] [DecidableEq k] (hqN : ¬ q ∣ N)
    (hmodel : R.IsModel) (hO : R.OrderLawFixed)
    (W : Finset (Place k (modularFunctionFieldC k N))) (hW : ∀ w ∈ W, w ∈ ssPlaces q N k)
    (hreg : R.RegularityLaw W) (hval : R.NodeValueLaw W)
    (w : Place k (modularFunctionFieldC k N)) (hw : w ∈ W)
    (hvalA : R.ValueIntegralityLaw w)
    (K₀ : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K₀]
    (hK₀fix : ∀ σ ∈ A.inertiaSubgroupIn ℚ, ∀ z ∈ K₀, σ z = z)
    (hϖq₀ : ∀ d : ↥(NodeLocalized.coeffSubring A K₀),
        NodeLocalized.redRestrict red K₀ d = 0 ↔
          ∃ d', d = ((q : ℕ) : ↥(NodeLocalized.coeffSubring A K₀)) * d')
    (c₁ : R.NodeCoordinates K₀ w) (E₀ : ℕ) (u₀ : ↥(R.nodeIntegersOver K₀ w)) (hu₀ : IsUnit u₀)
    (hxy₁ : c₁.x * c₁.y = R.nodeConst K₀ w ((q : ℕ) : ↥(NodeLocalized.coeffSubring A K₀)) ^ E₀ * u₀)
    (c_val : A) (hc : c_val ∈ IsLocalRing.maximalIdeal A)
    (hcE₀ : ∃ m ∈ IsLocalRing.maximalIdeal A, c_val * m = ((q : ℕ) : A) ^ E₀) :
    ∃! V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)),
      P.reduceFst V = w ∧
        V.HasValue (↑c₁.y : ↥(modularFunctionFieldBar (N * q))) (c_val : AlgebraicClosure ℚ) := by sorry
