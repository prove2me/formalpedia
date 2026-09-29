-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_valuation_pow_le_mul_prod_and_rigid_of_twist_levelOne
-- name    : ModularCurve.PlaceSpecialization.ProlongationTuple.valuation_pow_le_mul_prod_and_rigid_of_twist_levelOne
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.056571+00:00
-- url     : https://prove2.me/theorems/83723249-9b38-506b-b5cc-a7c898042e3c
-- title:
--   Twisted chord bounds and rigidity at a supersingular node
-- statement:
--   Fix a prime $q\ge 5$, a valuation subring $A$ of $\overline{\mathbb{Q}}$, an algebraically closed field $k$ of characteristic $q$ and a ring homomorphism $red:A\to k$ whose kernel is exactly the maximal ideal of $A$; fix modular polynomial data for $q$ satisfying the Kronecker congruence, integrality of the two degeneracy embeddings at level $1$ and prime $q$, a place specialization $P$ of $X_0$-type at level $1$, and a prolongation tuple $R$ over $P$ satisfying `IsModel` (the two divisor laws and the two cusp laws), the regularity law and node value law for a finite set $W$ of places of $\mathrm{modularFunctionFieldC}\,k\,1$ consisting precisely of the supersingular places (rational affine places whose $j$-value lies in the supersingular set), and the fixed-place order law. Fix a number field $K\subset\overline{\mathbb{Q}}$, a place $w\in W$ at which $R$ satisfies the value integrality law (every element of the node integers at $w$ has its value at each place $V$ over $w$ lying in $A$), an element $\varpi$ of $A\cap K$ generating the kernel of the reduction on $A\cap K$, an exponent $e_K\ge 1$ and a unit $\varepsilon$ with $q=\varpi^{e_K}\varepsilon$, and node coordinates $c=(x,y)$ over $K$ at $w$ (so $\mathrm{res}_1x=0$, $\mathrm{ord}_{\varphi w}\mathrm{res}_2x=1$, $\mathrm{res}_2y=0$, $\mathrm{ord}_w\mathrm{res}_1y=1$) together with a crossing presentation in the ring $\mathcal{O}$ of node integers over $K$ at $w$: an exponent $e_w\ge 1$ and a unit $u$ with $xy=\varpi^{e_we_K}u$, the ideal $(\varpi,x,y)$ being the unique maximal ideal of $\mathcal{O}$, the ideals $(\varpi,x)$ and $(\varpi,y)$ prime with $y\notin(\varpi,x)$ and $x\notin(\varpi,y)$, $\mathcal{O}$ Noetherian, and every element of $\mathcal{O}$ congruent to a constant modulo non-units. Let $f\ne 0$ in $\mathrm{modularFunctionFieldBar}(1\cdot q)$ and scalars $c_1,c_2\in\overline{\mathbb{Q}}$ be such that $c_1f$ lies in $R_1$'s integers with non-zero residue and $c_2f$ lies in $R_2$'s integers with non-zero residue, and let $e$ be a finitely supported integer-valued function on places $V$ of $\mathrm{modularFunctionFieldBar}(1\cdot q)$, supported on places with $P.\mathrm{reduceFst}\,V=w$ that are strict for neither side, with $0\le V.\mathrm{ord}\,f+e(V)$ for all such $V$. Writing $v_A$ for the valuation of $A$, $\Lambda=\prod_{V\in\operatorname{supp}e}v_A(y(V))^{e(V)}$, $o_1=\mathrm{ord}_w\mathrm{res}_1(c_1f)$, $o_2=\mathrm{ord}_{\mathrm{arithFrob}\cdot w}\mathrm{res}_2(c_2f)$ and $M=\sum_{V}e(V)$, the conclusion is the conjunction of $v_A(q)^{e_w(o_1+M)}\le v_A(c_1c_2^{-1})\Lambda$, of $v_A(c_1c_2^{-1})\Lambda\, v_A(q)^{e_wo_2}\le 1$, and of the rigidity assertion that if either of these two inequalities is an equality then $V.\mathrm{ord}\,f+e(V)=0$ for every place $V$ over $w$ that is strict for neither side, and $o_1+M+o_2=0$.
--
--   This is the chord inequality and its rigidity clause for the supersingular annulus of the semistable model of $X_0(q)$ at a place above $q$, expressed entirely in the value group of $A$ and in the currency of prolongation tuples: the two inequalities bound the twisted end orders of a section against the ratio of the two Gauss normalisations, and equality forces the twisted divisor to vanish along the annulus. It is the form used by [`ModularCurve.PlaceSpecialization.ProlongationTuple.AnnulusDatumQ.exists_chord_le_endOrders_and_rigid_of_isTwistOf_of_inertiaStable`](thm.html#ModularCurve.PlaceSpecialization.ProlongationTuple.AnnulusDatumQ.exists_chord_le_endOrders_and_rigid_of_isTwistOf_of_inertiaStable), where it is applied to annulus data attached to inertia-stable twists.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_valuation_pow_le_mul_prod_and_rigid_of_twist_levelOne.lean

import Mathlib
import Definitions.Def_ModularCurve_ProlongationTuple
import Definitions.Def_ModularCurve_NodeLocalizedPlaces
import Definitions.Def_ModularCurve_NodeDepth

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
set_option autoImplicit false
open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.PlaceSpecialization

theorem ModularCurve.PlaceSpecialization.ProlongationTuple.valuation_pow_le_mul_prod_and_rigid_of_twist_levelOne
    {q : ℕ} [Fact q.Prime] (hq5 : 5 ≤ q) {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
    (P : PlaceSpecialization A q 1 data hKr k red hα hβ)
    {W : Finset (Place k (modularFunctionFieldC k 1))}
    (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q 1 k)
    (R : ProlongationTuple P) (hR : R.IsModel) (hRL : R.RegularityLaw W) (hNV : R.NodeValueLaw W)
    (hO : R.OrderLawFixed)
    (hker : ∀ c : A, red c = 0 ↔ c ∈ IsLocalRing.maximalIdeal A)

    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ ↥K]
    (w : Place k (modularFunctionFieldC k 1)) (hw : w ∈ W) (hVI : R.ValueIntegralityLaw w)
    (ϖ : ↥(NodeLocalized.coeffSubring A K))
    (hϖ : ∀ d : ↥(NodeLocalized.coeffSubring A K), NodeLocalized.redRestrict red K d = 0 ↔ ∃ d', d = ϖ * d')
    (eK : ℕ) (heK : 1 ≤ eK) (ε : ↥(NodeLocalized.coeffSubring A K)) (hε : IsUnit ε)
    (hqϖ : ((q : ℕ) : ↥(NodeLocalized.coeffSubring A K)) = ϖ ^ eK * ε)
    (c : R.NodeCoordinates K w) (ew : ℕ) (hew : 1 ≤ ew)
    (u : ↥(R.nodeIntegersOver K w)) (hu : IsUnit u)
    (hxy : c.x * c.y = R.nodeConst K w ϖ ^ (ew * eK) * u)
    (hmax : (Ideal.span {R.nodeConst K w ϖ, c.x, c.y}).IsMaximal ∧
        ∀ M : Ideal ↥(R.nodeIntegersOver K w), M.IsMaximal → M = Ideal.span {R.nodeConst K w ϖ, c.x, c.y})
    (hbr : (Ideal.span {R.nodeConst K w ϖ, c.x}).IsPrime ∧ (Ideal.span {R.nodeConst K w ϖ, c.y}).IsPrime ∧
        c.y ∉ Ideal.span {R.nodeConst K w ϖ, c.x} ∧ c.x ∉ Ideal.span {R.nodeConst K w ϖ, c.y})
    (hnoeth : IsNoetherianRing ↥(R.nodeIntegersOver K w))
    (hres : ∀ g : ↥(R.nodeIntegersOver K w), ∃ o : ↥(NodeLocalized.coeffSubring A K), ¬ IsUnit (g - R.nodeConst K w o))

    (f : ↥(modularFunctionFieldBar (1 * q))) (hf0 : f ≠ 0)
    (c₁ c₂ : AlgebraicClosure ℚ) (h₁ : c₁ • f ∈ R.R₁.integers) (hr₁ : R.R₁.residue ⟨c₁ • f, h₁⟩ ≠ 0)
    (h₂ : c₂ • f ∈ R.R₂.integers) (hr₂ : R.R₂.residue ⟨c₂ • f, h₂⟩ ≠ 0)

    (e : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) →₀ ℤ)
    (he : ∀ V, e V ≠ 0 → P.reduceFst V = w ∧ ¬ P.IsStrictFst V ∧ ¬ P.IsStrictSnd V)
    (hpole : ∀ V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)),
      P.reduceFst V = w → ¬ P.IsStrictFst V → ¬ P.IsStrictSnd V → 0 ≤ V.ord f + e V) :

    A.valuation ((q : ℕ) : AlgebraicClosure ℚ) ^
        ((ew : ℤ) * (w.ord (R.residue₁ ⟨c₁ • f, h₁⟩) + ∑ V ∈ e.support, e V)) ≤
      A.valuation (c₁ * c₂⁻¹) *
        ∏ V ∈ e.support, A.valuation (V.evalAt (c.y : ↥(modularFunctionFieldBar (1 * q)))) ^ e V ∧

    A.valuation (c₁ * c₂⁻¹) *
        (∏ V ∈ e.support, A.valuation (V.evalAt (c.y : ↥(modularFunctionFieldBar (1 * q)))) ^ e V) *
        A.valuation ((q : ℕ) : AlgebraicClosure ℚ) ^
          ((ew : ℤ) * (arithFrobC q k 1 • w).ord (R.residue₂ ⟨c₂ • f, h₂⟩)) ≤ 1 ∧

    ((A.valuation ((q : ℕ) : AlgebraicClosure ℚ) ^
          ((ew : ℤ) * (w.ord (R.residue₁ ⟨c₁ • f, h₁⟩) + ∑ V ∈ e.support, e V)) =
        A.valuation (c₁ * c₂⁻¹) *
          ∏ V ∈ e.support, A.valuation (V.evalAt (c.y : ↥(modularFunctionFieldBar (1 * q)))) ^ e V ∨
      A.valuation (c₁ * c₂⁻¹) *
          (∏ V ∈ e.support, A.valuation (V.evalAt (c.y : ↥(modularFunctionFieldBar (1 * q)))) ^ e V) *
          A.valuation ((q : ℕ) : AlgebraicClosure ℚ) ^
            ((ew : ℤ) * (arithFrobC q k 1 • w).ord (R.residue₂ ⟨c₂ • f, h₂⟩)) = 1) →
      (∀ V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)),
          P.reduceFst V = w → ¬ P.IsStrictFst V → ¬ P.IsStrictSnd V → V.ord f + e V = 0) ∧
        w.ord (R.residue₁ ⟨c₁ • f, h₁⟩) + (∑ V ∈ e.support, e V) +
          (arithFrobC q k 1 • w).ord (R.residue₂ ⟨c₂ • f, h₂⟩) = 0) := by sorry
