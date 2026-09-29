-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_mem_range_redRestrict_of_hasValue_nodeResidueFst_levelOne_of_five_le
-- name    : ModularCurve.PlaceSpecialization.ProlongationTuple.mem_range_redRestrict_of_hasValue_nodeResidueFst_levelOne_of_five_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:45.66333+00:00
-- url     : https://prove2.me/theorems/56db8dff-8790-5f40-a751-2cf5a8de9db9
-- title:
--   Descent of node values of first residues at level one
-- statement:
--   Fix a prime $q$, a valuation subring $A$ of $\overline{\mathbb{Q}}$, a field $k$ of characteristic $q$ which is algebraically closed, and a ring homomorphism $\mathrm{red}\colon A \to k$; fix modular polynomial data for $q$ (a monic bivariate $\Phi$ over $\mathbb{Z}$ of degree $\psi(q)$ annihilating the pair $(j, j_q)$) satisfying the Kronecker congruence, together with the hypotheses that the Hecke $\bar\alpha$- and $\bar\beta$-maps at level $1$ and prime $q$ over $\overline{\mathbb{Q}}$ are integral, a place specialisation $P$ of this data at level $N=1$, and a prolongation tuple $R$ over $P$. Assume $5 \le q$. Let $K \subseteq \overline{\mathbb{Q}}$ be an intermediate field of finite degree over $\mathbb{Q}$, and let $w$ be a place of the modular function field $\mathrm{modularFunctionFieldC}\ k\ 1$ over $k$ lying in $\mathrm{ssPlaces}\ q\ 1\ k$, i.e. satisfying `IsSupersingularPlace q 1 k`. Assume the value $w.\mathrm{evalAt}$ of the canonical generator $\mathrm{jGeomGen}\ k\ 1$ (the residue at $w$ of the reduced $j$-function, or $0$ if $j$ is not $w$-integral) lies in the image of the subring $\mathrm{coeffSubring}\ A\ K$ under `NodeLocalized.redRestrict red K`, the composite of the inclusion into $A$ with $\mathrm{red}$. Let $g$ belong to the subring $R.\mathrm{nodeIntegersOver}\ K\ w$ of $\mathrm{modularFunctionFieldBar}(1\cdot q)$, consisting of the elements of $R.\mathrm{nodeIntegers}\ w$ whose Laurent expansion lies in $\mathrm{NodeLocalized.fieldOver}(1\cdot q)\ K$. Finally let $a \in k$ be such that the first residue $R.\mathrm{nodeResidue}_1\ w$ of $g$, an element of $\mathrm{modularFunctionFieldC}\ k\ 1$, has value $a$ at $w$, that is, it lies in the valuation subring of $w$ and its image in the residue field of $w$ is the image of $a$ under $k \to w.\mathrm{ResidueField}$. Then $a$ itself lies in the image of $\mathrm{coeffSubring}\ A\ K$ under `NodeLocalized.redRestrict red K`.
--
--   This is the descent step in the analysis of residues at supersingular nodes of $X_0(q)$ in characteristic $q$: values at such a node of first residues of $K$-rational members of the node ring are reductions of elements of the coefficient ring attached to $A$ and $K$. It is used by [`ModularCurve.PlaceSpecialization.ProlongationTuple.exists_not_isUnit_sub_nodeConst_of_evalAt_mem_range_redRestrict_levelOne_of_five_le`](thm.html#ModularCurve.PlaceSpecialization.ProlongationTuple.exists_not_isUnit_sub_nodeConst_of_evalAt_mem_range_redRestrict_levelOne_of_five_le), in the construction of functions with prescribed behaviour at a supersingular node.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_mem_range_redRestrict_of_hasValue_nodeResidueFst_levelOne_of_five_le.lean

import Definitions.Def_ModularCurve_NodeLocalizedPlaces

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve
open ModularCurve.PlaceSpecialization ModularCurve.PlaceSpecialization.ProlongationTuple

theorem ModularCurve.PlaceSpecialization.ProlongationTuple.mem_range_redRestrict_of_hasValue_nodeResidueFst_levelOne_of_five_le
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {P : PlaceSpecialization A q 1 data hKr k red hα hβ}
    (R : ProlongationTuple P) [IsAlgClosed k] [DecidableEq k] (hq : 5 ≤ q)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    (w : Place k (modularFunctionFieldC k 1)) (hw : w ∈ ssPlaces q 1 k)
    (hKres : w.evalAt (jGeomGen k 1) ∈ Set.range (NodeLocalized.redRestrict red K))
    (g : ↥(R.nodeIntegersOver K w)) (a : k)
    (ha : w.HasValue (R.nodeResidue₁ w ⟨g, g.2.1⟩ : ↥(modularFunctionFieldC k 1)) a) :
    a ∈ Set.range (NodeLocalized.redRestrict red K) := by sorry
