-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_hasValue_nodeResidueFst_red_evalAt_of_orderLawFixed
-- name    : ModularCurve.PlaceSpecialization.ProlongationTuple.hasValue_nodeResidueFst_red_evalAt_of_orderLawFixed
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:45.66333+00:00
-- url     : https://prove2.me/theorems/46377b8c-b84b-58e1-8eab-38099ca1f576
-- title:
--   Node residue of the first prolongation equals reduced value at V
-- statement:
--   Fix a prime $q$, a valuation subring $A$ of $\overline{\mathbb{Q}}$, a positive integer $N$, a field $k$ of characteristic $q$ that is algebraically closed, and a ring homomorphism $\mathrm{red} : A \to k$; fix modular polynomial data `data` for $q$ satisfying the Kronecker congruence `hKr`, integrality hypotheses $h\alpha$, $h\beta$ for the two degeneracy maps $\overline{F}_N \to \overline{F}_{Nq}$ on Laurent-series modular function fields, and a place specialisation $P$ of these data. Let $R$ be a prolongation tuple over $P$ (a pair of regular prolongations $R_1,R_2$ of $A$ in $\overline{F}_{Nq}$ together with the compatibilities recorded in `ProlongationTuple`). Assume $q \nmid N$; assume $R$ satisfies `IsModel` (the two divisor laws and the two cusp laws) and the fixed-place order law `OrderLawFixed`: for $f$ integral for both $R_1$ and $R_2$ with both residues nonzero, $D$ the divisor of $f$, and every place $v$ of $F_N^{(k)}$ fixed by the square of `frobOnPlacesGeomLevel` at which $j$ and $j_N$ are integral, the pushforward of $D$ along `P.reduceFst` has value at $v$ equal to $\mathrm{ord}_v$ of the first residue of $f$ plus $\mathrm{ord}$ of the second residue at the Frobenius image of $v$. Let $W$ be a finite set of places of $F_N^{(k)}$ all lying in `ssPlaces q N k` (rational, affine in $j,j_N$, with $j$-value in the supersingular set), and assume the regularity law and the node-value law of $R$ along $W$. Let $K$ be a finite extension of $\mathbb{Q}$ inside $\overline{\mathbb{Q}}$, let $w \in W$, and assume the value-integrality law at $w$: every element of the node ring $R.\mathrm{nodeIntegers}\,w$ has $V$-value in $A$ for every place $V$ of $\overline{F}_{Nq}$ over $\overline{\mathbb{Q}}$ with $P.\mathrm{reduceFst}\,V = w$. Finally let $g$ lie in $R.\mathrm{nodeIntegersOver}\,K\,w$, i.e. $g$ lies in the node ring at $w$ and its Laurent expansion lies in the subfield generated over the constants of $K$ by $j$ and $j_N$, and let $V$ be a place of $\overline{F}_{Nq}$ with $P.\mathrm{reduceFst}\,V = w$. Then the element `nodeResidue₁ w` of $g$ (viewed in $F_N^{(k)}$) is integral at $w$ and its residue at $w$ equals the image in the residue field of $w$ of $\mathrm{red}$ applied to the value $V.\mathrm{evalAt}\,g \in A$.
--
--   This is the compatibility between reduction of values and the residue map at a supersingular node: evaluating an element of the node ring at a characteristic-zero place $V$ above $w$ and then reducing by $\mathrm{red}$ gives the same element of $k$ as passing to the first residue and evaluating at $w$. It is used in the computation of crossing exponents at supersingular points and in the construction of uniformisers with prescribed order along the first component.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_hasValue_nodeResidueFst_red_evalAt_of_orderLawFixed.lean

import Definitions.Def_ModularCurve_NodeDepth

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve
open ModularCurve.PlaceSpecialization
open ModularCurve.PlaceSpecialization.ProlongationTuple

theorem ModularCurve.PlaceSpecialization.ProlongationTuple.hasValue_nodeResidueFst_red_evalAt_of_orderLawFixed
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    {P : PlaceSpecialization A q N data hKr k red hα hβ}
    (R : ProlongationTuple P) [IsAlgClosed k] [DecidableEq k] (hqN : ¬ q ∣ N)
    (hmodel : R.IsModel) (hord : R.OrderLawFixed)
    (W : Finset (Place k (modularFunctionFieldC k N))) (hW : ∀ w ∈ W, w ∈ ssPlaces q N k)
    (hreg : R.RegularityLaw W) (hval : R.NodeValueLaw W)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    (w : Place k (modularFunctionFieldC k N)) (hw : w ∈ W)
    (hvalA : R.ValueIntegralityLaw w)
    (g : ↥(R.nodeIntegersOver K w))
    (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)))
    (hV : P.reduceFst V = w) :
    w.HasValue (R.nodeResidue₁ w ⟨g, g.2.1⟩ : modularFunctionFieldC k N)
      (red ⟨V.evalAt (g : ↥(modularFunctionFieldBar (N * q))),
        hvalA (g : ↥(modularFunctionFieldBar (N * q)))
          (R.nodeIntegersOver_le K w g.2) V hV⟩) := by sorry
