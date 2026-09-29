-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_exists_inertiaStable_rep_redFst_redSnd_notMem_of_forall_notMem_ssPlaces
-- name    : ModularCurve.PlaceSpecialization.LevelOneProlongationPair.exists_inertiaStable_rep_redFst_redSnd_notMem_of_forall_notMem_ssPlaces
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:44.572352+00:00
-- url     : https://prove2.me/theorems/9f15d23d-9d54-516b-967f-9839669ac704
-- title:
--   Inertia-stable representatives of J₀(q)^{I_A} avoiding a finite place set
-- statement:
--   Fix a prime $q$ and a valuation subring $A$ of $\overline{\mathbf Q}$ whose residue field $k = \mathrm{ResidueField}\,A$ has characteristic $q$; let $\mathrm{data}$ be modular polynomial data for $q$ (a monic $\Phi$ of degree $\psi(q)$ annihilating the pair of $q$-expansions of $j$) satisfying the Kronecker congruence $hKr$, namely that $\Phi$ reduced modulo $q$ equals $(C(X)^q - X)(C(X) - X^q)$, and let $h\alpha$, $h\beta$ assert integrality of the two degeneracy embeddings $\mathrm{heckeAlphaBar}$, $\mathrm{heckeBetaBar}$ from level $1$ to level $1\cdot q$ over $\overline{\mathbf Q}$. Let $P$ be a place specialization of level $1$ for $A$, $q$, these data, with target field $k$ and reduction the residue map of $A$, and let $R$ be a level-one prolongation pair for $P$ subject to: $hR$, the model laws (the two divisor laws for $\mathrm{redFst}$, $\mathrm{redSnd}$ and the two cusp laws at the cusps $\infty$ and $0$); $hO$, the order law at places fixed by the square of geometric Frobenius; $hval$, the node value law for $q$ and the residue map; and $hNR$, the regularity law relative to a finset $S₀$ of $k$ whose elements are exactly the supersingular $j$-values $\mathrm{ssJSet}\,q\,k$ (those $j$ for which every elliptic curve over $k$ with invariant $j$ has no nonzero $q$-torsion point). Let $T$ be a finset of places of $\mathrm{modularFunctionFieldC}\,k\,1$, none of which is supersingular for $q$ at level $1$, and let $x$ be an element of $\mathrm{inertiaInvariants}\,A\,(1\cdot q)$, i.e. a class in $\mathrm{Pic}^0$ of $\mathrm{modularFunctionFieldBar}(1\cdot q)$ over $\overline{\mathbf Q}$ fixed by every $\sigma$ in the inertia subgroup $A.\mathrm{inertiaSubgroupIn}\,\mathbf Q$ acting through $\mathrm{arithmeticGalois}$. The conclusion provides a degree-zero divisor $E$ on $\mathrm{modularFunctionFieldBar}(1\cdot q)$ whose class is $x$, such that $\mathrm{arithmeticGalois}$ applied to each $\sigma$ in that inertia subgroup fixes $E$ as a divisor, and such that for every place $V$ in the support of $E$ both reductions $P.\mathrm{redFst}\,V$ and $P.\mathrm{redSnd}\,V$ lie outside $T$.
--
--   This is the residue-field form of the statement that an inertia-invariant class of $J_0(q)$ over $\overline{\mathbf Q}$ admits a representative divisor that is merely stable (not pointwise fixed) under inertia and whose support avoids prescribed residue discs, the excluded places being packaged as a finite set $T$ of non-supersingular places of the $j$-line in characteristic $q$. It feeds the class-level statement about degree-zero representatives whose support points are of strict type or reduce into a prescribed set, which is where the component-group specialization of $J_0(q)$ at $q$ is evaluated.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_exists_inertiaStable_rep_redFst_redSnd_notMem_of_forall_notMem_ssPlaces.lean

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

theorem ModularCurve.PlaceSpecialization.LevelOneProlongationPair.exists_inertiaStable_rep_redFst_redSnd_notMem_of_forall_notMem_ssPlaces
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
    (x : ↥(inertiaInvariants A (1 * q))) :
    ∃ E : ↥(Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar (1 * q)))),
      Pic0.mk E = (x : JZero (1 * q)) ∧
        (∀ σ ∈ A.inertiaSubgroupIn ℚ,
          arithmeticGalois (modularFunctionFieldFull (1 * q)) σ •
            (E : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))) = E) ∧
        ∀ V ∈ (E : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))).support,
          P.redFst V ∉ T ∧ P.redSnd V ∉ T := by sorry
