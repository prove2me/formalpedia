-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_AnnulusDatumQ_spData_mem_admissible
-- name    : ModularCurve.PlaceSpecialization.ProlongationTuple.AnnulusDatumQ.spData_mem_admissible
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:44.572352+00:00
-- url     : https://prove2.me/theorems/1020f11a-b2e6-5e7f-97c8-87846ccb53e8
-- title:
--   Admissibility of the twisted gluing datum at level one
-- statement:
--   Fix a prime $q$, a valuation subring $A$ of $\overline{\mathbf Q}$, an algebraically closed perfect field $k$ of characteristic $q$, a ring homomorphism $red : A \to k$, modular polynomial data `data` for $q$ satisfying the Kronecker congruence $hKr$ (the reduction mod $q$ of $\Phi$ equals $(C(X)^q - X)(C(X) - X^q)$), and hypotheses $h\alpha$, $h\beta$ asserting that the two degeneracy embeddings $\overline{\mathcal F}(1) \to \overline{\mathcal F}(q)$ of base-changed modular function fields are integral. Let $P$ be a place specialisation of level $N = 1$ for these data, $R$ a prolongation tuple for $P$, and $W$ a finite set of places of $\mathrm{modularFunctionFieldC}\ k\ 1$ whose members are exactly the supersingular places `ssPlaces q 1 k`. Let `dat` be an orbit annulus datum for $R$ over $W$ whose distinguished place `dat.cusp` lies outside $W$ and is fixed by the semilinear arithmetic Frobenius $\varphi =$ `arithFrobC q k 1`, let $a$ be a twist vector for $W$, and let $D$ be a divisor on $\overline{\mathcal F}(1 \cdot q)$. Then the gluing datum `dat.spData a D` is admissible for the node pairs $(w, \varphi \cdot w)$, $w \in W$: its two divisor components, namely $\mathrm{reduceFst}_*(\mathrm{fstDiv}\,D)$ and $\mathrm{reduceSnd}_*(\mathrm{sndDiv}\,D)$ each corrected by subtracting their degree times the cusp, have degree zero, the first vanishes at every $w \in W$ and the second at every $\varphi \cdot w$. The unit component `dat.nodeUnitOf a D` is unconstrained by admissibility.
--
--   Admissibility is the condition under which a pair of divisors together with units at the nodes defines a class in the glued Picard group of the semistable fibre of $X_0(q)$ at $q$, the two components of that fibre being copies of the $j$-line crossing at the supersingular points. This verification is used in the construction of fixed strict twisted classes in the kernel of the specialisation map.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_AnnulusDatumQ_spData_mem_admissible.lean

import Mathlib
import Definitions.Def_ModularCurve_LevelOneGlueData
import Definitions.Def_AlgebraicCurve_GluedPic0
import Definitions.Def_ModularCurve_NodeDepth
import Definitions.Def_ModularCurve_NodeLocalizedPlaces
import Definitions.Def_ModularCurve_ProlongationTuple
import Definitions.Def_ModularCurve_LevelOneAnnulusSpecialization
import Definitions.Def_ModularCurve_LevelOneAnnulusSpecializationOrbit

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.PlaceSpecialization

theorem ModularCurve.PlaceSpecialization.ProlongationTuple.AnnulusDatumQ.spData_mem_admissible
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] [PerfectField k] [IsAlgClosed k] [DecidableEq k] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {P : PlaceSpecialization A q 1 data hKr k red hα hβ} {R : P.ProlongationTuple}
    {W : Finset (Place k (modularFunctionFieldC k 1))} (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q 1 k)
    (dat : R.AnnulusDatumQ W) (hcusp : dat.cusp ∉ W) (hcuspφ : arithFrobC q k 1 • dat.cusp = dat.cusp)
    (a : ProlongationTuple.TwistVector (k := k) W)
    (D : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))) :
    dat.spData a D ∈ GluingData.admissible (nodePairsOfPlaces (arithFrobC q k 1) W) := by sorry
