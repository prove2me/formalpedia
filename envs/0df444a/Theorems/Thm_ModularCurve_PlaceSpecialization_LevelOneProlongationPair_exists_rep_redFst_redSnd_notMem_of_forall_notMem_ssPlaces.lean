-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_exists_rep_redFst_redSnd_notMem_of_forall_notMem_ssPlaces
-- name    : ModularCurve.PlaceSpecialization.LevelOneProlongationPair.exists_rep_redFst_redSnd_notMem_of_forall_notMem_ssPlaces
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:44.572352+00:00
-- url     : https://prove2.me/theorems/a28deb40-d41b-5f62-bca1-7caf6217b9ca
-- title:
--   Moving representatives of J₀(q)-classes off a finite place set
-- statement:
--   Fix a prime $q$ and a valuation subring $A$ of $\overline{\mathbb Q}$ whose residue field $\kappa=$ `ResidueField A` has characteristic $q$. Let `data` consist of a monic $\Phi\in\mathbb Z[X][Y]$ of degree $\psi(q)$ vanishing on the pair $(j,j_q)$ of $q$-expansions, let `hKr` assert the Kronecker congruence $\Phi \equiv (C(X)^q-X)(C(X)-X^q) \bmod q$, and let `hα`, `hβ` assert that the two degeneracy inclusions `heckeAlphaBar`, `heckeBetaBar` from level $1$ into level $1\cdot q$ are integral ring maps. Let $P$ be a `PlaceSpecialization` for $A$, $q$, level $1$, this data, with target field $\kappa$ and reduction the residue map of $A$; it provides maps `P.redFst`, `P.redSnd` sending a place $V$ of $\overline{\mathbb Q}(X_0(q))$ to the place $P.\mathrm{sp}$ of the restriction of $V$ along `heckeAlphaBar`, resp. `heckeBetaBar`. Let $R$ be a `LevelOneProlongationPair` for $P$ (a pair of regular prolongations $R_1,R_2$ of $A$ to the level-$q$ function field, interchanged by the Fricke involution, together with the compatible reduction maps $\overline{\mathrm{red}}$ and $\iota$ on residue data) satisfying: `hR`, the model laws `DivisorLawFst`, `DivisorLawSnd`, `CuspLawInfty`, `CuspLawZero`, expressing that the pushforwards under `P.redFst`, `P.redSnd` of the divisor of a function $f$, restricted to the relevant strict-type and cusp-side parts, compute the orders of the two residues of $f$; `hO`, the law `OrderLawFixed` doing the same at the places fixed by the square of the geometric Frobenius on places and distinct from `P.redFst (cuspInftyBar (1*q))`, with the two contributions added; `hval`, the `NodeValueLaw` for $q$ and the residue map of $A$; and `hNR`, the `RegularityLaw` for a finite set $S_0\subseteq\kappa$ which is assumed (via `hS₀`) to consist exactly of the supersingular $j$-invariants, i.e. the $j$ for which every elliptic curve over $\kappa$ with that $j$-invariant has trivial $q$-torsion. Finally let $T$ be a finite set of places of `modularFunctionFieldC κ 1` none of which is supersingular (rational, affine geometric, with $j$-value in `ssJSet q κ`), and let $x$ be a class in $J_0(q)=$ `JZero (1*q)`, the degree-zero divisor class group of `modularFunctionFieldBar (1*q)` over $\overline{\mathbb Q}$. Then there is a degree-zero divisor $E$ with class $x$ such that for every place $V$ in the support of $E$ one has `P.redFst V ∉ T` and `P.redSnd V ∉ T`.
--
--   This is the moving lemma for divisor classes on $J_0(q)$ in its level-one, lawful-pair form: every class is represented by a degree-zero divisor whose support reduces away from a prescribed finite set of non-supersingular places of the $j$-line in characteristic $q$. It is used by [`ModularCurve.PlaceSpecialization.exists_rep_reduce_notMem_of_moving_of_disjoint_levelOne`](thm.html#ModularCurve.PlaceSpecialization.exists_rep_reduce_notMem_of_moving_of_disjoint_levelOne), which removes the hypotheses on the prolongation pair by supplying them for an arbitrary place specialization.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_exists_rep_redFst_redSnd_notMem_of_forall_notMem_ssPlaces.lean

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

theorem ModularCurve.PlaceSpecialization.LevelOneProlongationPair.exists_rep_redFst_redSnd_notMem_of_forall_notMem_ssPlaces
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
    (x : JZero (1 * q)) :
    ∃ E : ↥(Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar (1 * q)))),
      Pic0.mk E = x ∧
        ∀ V ∈ (E : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))).support,
          P.redFst V ∉ T ∧ P.redSnd V ∉ T := by sorry
