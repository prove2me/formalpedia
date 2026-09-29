-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_exists_ord_eq_one_forall_redFst_redSnd_notMem
-- name    : ModularCurve.PlaceSpecialization.LevelOneProlongationPair.exists_ord_eq_one_forall_redFst_redSnd_notMem
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:44.572352+00:00
-- url     : https://prove2.me/theorems/10344803-ed3e-58b9-bf2e-25afdf2b56f9
-- title:
--   One-point moving lemma on X₀(q) at level one
-- statement:
--   Fix a prime $q$ and a valuation subring $A$ of $\overline{\mathbb Q}$ whose residue field $\kappa=$ `ResidueField A` has characteristic $q$; write `red` for the residue map $A\to\kappa$. Let `data` be a `ModularPolynomialData q` (a monic $\Phi\in\mathbb Z[X][Y]$ of degree $\psi(q)$ annihilating the pair $(j,j_q)$ of $q$-expansions) satisfying the Kronecker congruence `hKr`, i.e. the reduction of $\Phi$ modulo $q$ equals $(C X^{q}-X)(C X-X^{q})$, and let `hα`, `hβ` assert that the two degeneracy embeddings `heckeAlphaBar`, `heckeBetaBar` of `modularFunctionFieldBar 1` into `modularFunctionFieldBar (1 * q)` are integral. Let $P$ be a `PlaceSpecialization` of this data over $\kappa$ with `red`, so that each place $W$ of `modularFunctionFieldBar (1 * q)` has two reductions $P.\mathrm{redFst}\,W$, $P.\mathrm{redSnd}\,W$, places of the level-one field `modularFunctionFieldC κ 1`, obtained by restricting $W$ along `heckeAlphaBar`, resp. `heckeBetaBar`, and applying $P.\mathrm{sp}$. Let $R$ be a level-one prolongation pair for $P$ (two regular prolongations $R_1,R_2$ of $A$ to `modularFunctionFieldBar (1 * q)` with values in the geometric level-one field over $\kappa$, interchanged by the Fricke involution, together with the comparison data). Assume: `hR`, that $R$ is a model, i.e. the two divisor laws and the two cusp laws, computing pushforwards along $\mathrm{redFst}$, $\mathrm{redSnd}$ of the divisor of a function integral with nonzero residues at $R_1,R_2$ in terms of the orders of the residues; `hO`, the order law at the places fixed by the square of the geometric Frobenius `frobOnPlacesGeomLevel` and distinct from $\mathrm{redFst}$ of the cusp at infinity; `hval`, the node value law for $q$ and the residue map of $A$; and `hNR`, the regularity law relative to a finset $S_0$ of $\kappa$ whose members are exactly the elements of `ssJSet q κ`, i.e. those $j\in\kappa$ such that every elliptic Weierstrass curve over $\kappa$ with invariant $j$ has no nonzero point killed by $q$. Let $T$ be a finite set of places of `modularFunctionFieldC κ 1`, none of which lies in `ssPlaces q 1 κ` (rational, affine geometric, and with value of the generator $j$ in `ssJSet q κ`), and let $V_0$ be a place of `modularFunctionFieldBar (1 * q)` with $P.\mathrm{redFst}\,V_0\in T$ or $P.\mathrm{redSnd}\,V_0\in T$. Then there exist a nonzero $f$ in `modularFunctionFieldBar (1 * q)` and a divisor $D$ with $D\,V=\operatorname{ord}_V f$ for every place $V$, such that $D\,V_0=1$ and for every $V$ in the support of $D$ with $V\neq V_0$ both $P.\mathrm{redFst}\,V\notin T$ and $P.\mathrm{redSnd}\,V\notin T$.
--
--   This is the one-point moving step for divisors on $X_0(q)$ over $\overline{\mathbb Q}$ at the prime $q$: a function with a simple zero at a prescribed point $V_0$ all of whose remaining zeros and poles reduce, on both branches of the special fibre, outside a prescribed finite set $T$ of non-supersingular places of the $j$-line in characteristic $q$. It feeds the choice of divisor-class representatives in [`ModularCurve.PlaceSpecialization.LevelOneProlongationPair.exists_rep_redFst_redSnd_notMem_of_forall_notMem_ssPlaces`](thm.html#ModularCurve.PlaceSpecialization.LevelOneProlongationPair.exists_rep_redFst_redSnd_notMem_of_forall_notMem_ssPlaces).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_exists_ord_eq_one_forall_redFst_redSnd_notMem.lean

import Mathlib
import Definitions.Def_ModularCurve_LevelOneProlongationPairRegularity
import Definitions.Def_ModularCurve_SupersingularNodes
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_ModularCurve_GlueData
import Definitions.Def_ModularCurve_CoeffSemilinearAut
import Definitions.Def_ValuationSubring_ReduceAt
import Definitions.Def_WeierstrassCurve_ReductionMap

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.PlaceSpecialization

theorem ModularCurve.PlaceSpecialization.LevelOneProlongationPair.exists_ord_eq_one_forall_redFst_redSnd_notMem
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    [CharP (ResidueField A) q] [DecidableEq (ResidueField A)]
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {P : PlaceSpecialization A q 1 data hKr (ResidueField A) (IsLocalRing.residue A) hα hβ}
    (R : P.LevelOneProlongationPair) (hR : R.IsModel) (hO : R.OrderLawFixed)
    (hval : LevelOneProlongationPair.NodeValueLaw q (IsLocalRing.residue A))
    (S₀ : Finset (ResidueField A)) (hS₀ : ∀ a, a ∈ S₀ ↔ a ∈ ssJSet q (ResidueField A))
    (hNR : R.RegularityLaw S₀)
    (T : Finset (Place (ResidueField A) ↥(modularFunctionFieldC (ResidueField A) 1)))
    (hT : ∀ t ∈ T, t ∉ ssPlaces q 1 (ResidueField A))
    (V₀ : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)))
    (hV₀ : P.redFst V₀ ∈ T ∨ P.redSnd V₀ ∈ T) :
    ∃ (f : ↥(modularFunctionFieldBar (1 * q)))
      (D : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))),
      f ≠ 0 ∧ (∀ V, D V = V.ord f) ∧ D V₀ = 1 ∧
        ∀ V ∈ D.support, V ≠ V₀ → P.redFst V ∉ T ∧ P.redSnd V ∉ T := by sorry
