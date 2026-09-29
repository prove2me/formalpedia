-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_isGluedPrincipal_glueData_of_forall_apply_eq_ord_of_regularityLaw_of_nodeValueLaw_of_nonempty
-- name    : ModularCurve.PlaceSpecialization.isGluedPrincipal_glueData_of_forall_apply_eq_ord_of_regularityLaw_of_nodeValueLaw_of_nonempty
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.056571+00:00
-- url     : https://prove2.me/theorems/db9638d0-4f66-52b0-a675-5e27d6f950cb
-- title:
--   Glued principality of the gluing datum of a principal divisor
-- statement:
--   Fix a prime $q$, a valuation subring $A$ of $\overline{\mathbb{Q}}$, a level $N \neq 0$, an algebraically closed field $k$ of characteristic $q$ and a ring homomorphism $red : A \to k$, together with modular polynomial data `data` for $q$ satisfying the Kronecker congruence $hKr$ (the reduction of $\Phi$ mod $q$ factors as $(Y^q - X)(Y - X^q)$) and integrality hypotheses $h\alpha$, $h\beta$ for the two degeneracy embeddings of level $N$ into level $Nq$ over $\overline{\mathbb{Q}}$. Assume $q \nmid N$, and let $P$ be a place specialization of the level-$N$ modular curve in this situation, $R$ a prolongation tuple for $P$ satisfying `R.IsModel` (the two divisor laws and the two cusp laws) and `R.OrderLawFixed` (the order law at Frobenius-fixed affine geometric places). Let $W$ be a nonempty finite set of places of `modularFunctionFieldC k N`, each supersingular in the sense of `ssPlaces q N k` (rational, affine geometric, with supersingular $j$-value), and assume $R$ satisfies the regularity law and the node-value law for $W$; write $S$ for the node pairs `nodePairsOfPlaces (arithFrobC q k N) W`, the image of $W$ under the embedding `smulNodePairEmb` attached to the coefficientwise arithmetic Frobenius. Let $f \neq 0$ in `modularFunctionFieldBar (N * q)`, let $D$ be its divisor ($D V = V.\mathrm{ord}\, f$ for every place $V$), assume $D$ is good for $P$ (every place in its support is strictly first- or strictly second-sided) and that the gluing datum `P.glueData S D` — the pair consisting of the push-forward along `P.reduceFst` of the strictly-first-sided part of $D$, the push-forward along `P.reduceSnd` of the strictly-second-sided part, and the zero unit component — is admissible (both divisors of degree zero and vanishing at the two coordinates of each node pair). Then this gluing datum is glued principal: there are nonzero $g_1, g_2$ in `modularFunctionFieldC k N` and families of units $a, b$ indexed by $S$ such that the first divisor is the divisor of $g_1$, the second the divisor of $g_2$, each $s \in S$ has $g_1$ taking the value $a_s$ at $s.1$ and $g_2$ taking the value $b_s$ at $s.2$, and $a_s / b_s = 1$ for all $s$, matching the zero unit component.
--
--   This is the well-definedness statement underlying the glued description of divisor classes on the special fibre at $q$ of the modular curve of level $Nq$, in the Deligne–Rapoport picture of two copies of the level-$N$ curve crossed at the supersingular points: the gluing datum of a principal divisor is principal in the glued sense. It is used by [`ModularCurve.PlaceSpecialization.exists_widths_componentMap_gluedSpecialization_placeWidthChar_of_isModel`](thm.html#ModularCurve.PlaceSpecialization.exists_widths_componentMap_gluedSpecialization_placeWidthChar_of_isModel).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_isGluedPrincipal_glueData_of_forall_apply_eq_ord_of_regularityLaw_of_nodeValueLaw_of_nonempty.lean

import Definitions.Def_ModularCurve_GlueData
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_ModularCurve_CoeffSemilinearAut
import Definitions.Def_ModularCurve_ProlongationTuple

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve

theorem ModularCurve.PlaceSpecialization.isGluedPrincipal_glueData_of_forall_apply_eq_ord_of_regularityLaw_of_nodeValueLaw_of_nonempty {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
  {N : ℕ} [NeZero N] {k : Type*} [Field k] [CharP k q] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
  {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
 [IsAlgClosed k] [DecidableEq k]
    (hqN : ¬ q ∣ N)
    (P : PlaceSpecialization A q N data hKr k red hα hβ)
    (R : PlaceSpecialization.ProlongationTuple P) (hmodel : R.IsModel) (hO : R.OrderLawFixed)
    (W : Finset (Place k (modularFunctionFieldC k N)))
    (hW : ∀ w ∈ W, w ∈ ssPlaces q N k) (hWne : W.Nonempty)
    (hreg : R.RegularityLaw W) (hnv : R.NodeValueLaw W)
    (f : modularFunctionFieldBar (N * q)) (hf : f ≠ 0)
    (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)))
    (hDf : ∀ V, D V = V.ord f) (hgood : P.IsGoodDiv D)
    (hadm : P.glueData (nodePairsOfPlaces (arithFrobC q k N) W) D
      ∈ GluingData.admissible (nodePairsOfPlaces (arithFrobC q k N) W)) :
    GluingData.IsGluedPrincipal (nodePairsOfPlaces (arithFrobC q k N) W)
      (P.glueData (nodePairsOfPlaces (arithFrobC q k N) W) D) := by sorry
