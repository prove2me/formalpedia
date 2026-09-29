-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_exists_ord_eq_one_forall_redFst_redSnd_notMem_forall_inertia_smul_eq_residueField
-- name    : ModularCurve.PlaceSpecialization.LevelOneProlongationPair.exists_ord_eq_one_forall_redFst_redSnd_notMem_forall_inertia_smul_eq_residueField
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:44.572352+00:00
-- url     : https://prove2.me/theorems/1095f255-5eaa-5e00-ad4e-f0c8be7f474b
-- title:
--   Inertia-equivariant one-point moving lemma on X₀(q)
-- statement:
--   Fix a prime $q$ and a valuation subring $A$ of $\overline{\mathbb Q}$ whose residue field has characteristic $q$, take $k=\mathrm{ResidueField}\,A$ with the residue map $A\to k$, and let `data` be modular polynomial data for $q$ satisfying the Kronecker congruence `hKr`, while `hα`, `hβ` assert integrality of the two degeneracy maps $\alpha,\beta$ from level $1$ to level $q$ after base change to $\overline{\mathbb Q}$. Let $P$ be a place specialization of level $1$ at $q$ for these data, valued in $k$, and let $R$ be a level-one prolongation pair for $P$ which is a model (the two divisor laws and the two cusp laws), satisfies the order law at places fixed by the square of geometric Frobenius, the node value law `hval` for $q$ and the residue map of $A$, and the regularity law relative to a finite set $S_0\subseteq k$ whose elements are exactly the supersingular $j$-invariants `ssJSet q k`. Let $T$ be a finite set of places of $k(\tilde\jmath)=$ `modularFunctionFieldC k 1` over $k$, no member of which is a supersingular place (rational, affine geometric, with supersingular $j$-value), and let $V_0$ be a place of `modularFunctionFieldBar (1 * q)` over $\overline{\mathbb Q}$ at least one of whose two level-one reductions `P.redFst V₀`, `P.redSnd V₀` lies in $T$. Then there exist a nonzero $f$ in `modularFunctionFieldBar (1 * q)` and a divisor $D$ with $D(V)=\mathrm{ord}_V(f)$ for every place $V$, such that $D(V_0)=1$, every $V\neq V_0$ in the support of $D$ has both reductions `P.redFst V` and `P.redSnd V` outside $T$, and for every $\sigma$ in the inertia subgroup of $A$ inside $\mathrm{Aut}(\overline{\mathbb Q}/\mathbb Q)$ whose induced semilinear automorphism `arithmeticGalois (modularFunctionFieldFull (1 * q)) σ` fixes the place $V_0$, that automorphism also fixes $f$.
--
--   This is the equivariant form of the one-point moving lemma on $X_0(q)$ in the level-one reduction setting: a function with a simple zero at a prescribed place, all of whose remaining zeros and poles reduce away from a prescribed finite set of non-supersingular places of the $j$-line, and which is invariant under the stabiliser of $V_0$ in the inertia group at $q$. It is used to produce inertia-stable representatives of divisor classes avoiding a bad finite set, in the study of the reduction of $J_0(q)$ at $q$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_exists_ord_eq_one_forall_redFst_redSnd_notMem_forall_inertia_smul_eq_residueField.lean

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

theorem ModularCurve.PlaceSpecialization.LevelOneProlongationPair.exists_ord_eq_one_forall_redFst_redSnd_notMem_forall_inertia_smul_eq_residueField
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
        (∀ V ∈ D.support, V ≠ V₀ → P.redFst V ∉ T ∧ P.redSnd V ∉ T) ∧
        ∀ σ ∈ A.inertiaSubgroupIn ℚ,
          arithmeticGalois (modularFunctionFieldFull (1 * q)) σ • V₀ = V₀ →
            arithmeticGalois (modularFunctionFieldFull (1 * q)) σ • f = f := by sorry
