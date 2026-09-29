-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_exists_forall_mem_dom_teleChart_eIg_arithmeticGalois_smul_of_inertiaIgusaInftyClause
-- name    : ModularCurve.FullLevel.exists_forall_mem_dom_teleChart_eIg_arithmeticGalois_smul_of_inertiaIgusaInftyClause
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:33.630704+00:00
-- url     : https://prove2.me/theorems/31aabe43-c358-52d2-8140-2c71b6e7b8f0
-- title:
--   Inertia permutes the Igusa chart domains of a semistable covering
-- statement:
--   Fix a prime $q\ge 5$, a non-zero natural number $M'$ with $q\nmid M'$, and a prime $\mathrm{lam}$ distinct from $q$. Assume [`ModularCurve.FullLevel.LevelAutInputs q M'`](def/ModularCurve_FullLevelJacobian.html#L220) (for every index $\zeta$ and every $\gamma\in\Gamma_0(M')$ there is an automorphism of `fieldBar q M'` over $\overline{\mathbb Q}$ satisfying `IsLevelAutBar`) and [`ModularCurve.FullLevel.GL2Laws q M'`](def/ModularCurve_FullLevelJacobian.html#L255) (a monoid homomorphism from $GL_2(\mathbb Z/q)$ to the endomorphisms of the Jacobian realising `slJac` on reductions of $\Gamma_0(M')$-matrices and `diagJac` on the elements `diagOneElem`). Let $P$ be a valuation subring of $\overline{\mathbb Q}$ with $q$ a non-unit of $P$, let $W$ be a finite set of places of $\mathrm{modularFunctionFieldC}(\kappa_P, M')$ over the residue field $\kappa_P$ whose members are exactly the supersingular places [`ModularCurve.ssPlaces q M'`](def/ModularCurve_SupersingularNodePlaces.html#L113), let $\pi\in P$ satisfy $\pi^{q^2-1}=q$, and let $\iota:\mathbb F_{q^2}\to\kappa_P$ be a ring homomorphism, used as the algebra structure on $\kappa_P$; the coordinate ring [`DrinfeldCurve.CoordRing q`](def/DrinfeldCurve_CoordRing.html#L21) $\kappa_P$ is assumed to be a domain. Assume $\mathrm{modularFunctionFieldBar}\,M'\le \mathrm{fieldBar}\,q\,M'$ via `hle`, and let $R_0$ be a constant reduction of $\mathrm{modularFunctionFieldBar}\,M'$ to $\mathrm{modularFunctionFieldC}(\kappa_P,M')$ relative to $P$ such that every Laurent series $y$ over $P$ whose coefficientwise image in $\overline{\mathbb Q}$ lies in $\mathrm{modularFunctionFieldBar}\,M'$ lies in $R_0.\mathrm{integers}$ and has $R_0$-residue equal, as a Laurent series over $\kappa_P$, to the coefficientwise reduction of $y$. Then for every semistable covering $\mathcal C$ of type [`ModularCurve.FullLevel.SemistableCovering q M' P W`](def/ModularCurve_FullLevelSemistableCovering.html#L28) satisfying the equivalence clauses, the $W_2$ clauses for $\pi$, $\iota$ with exponent $\eta=q$, the level-pinning clauses for `hle` and $R_0$, the inertia clause for $\pi$, the width clause for $\pi$, the genus, discrete-fibre, curve and naturality clauses, and the inertia–Igusa clause at $\infty$, the following holds: for every $\tau$ in the inertia subgroup of $P$ over $\mathbb Q$ and every line $\ell\in\mathbb P^1(\mathbb F_q)$ there is a line $\ell'\in\mathbb P^1(\mathbb F_q)$ such that every place $Q$ of $\mathrm{fieldBar}\,q\,M'$ over $\overline{\mathbb Q}$ lying in the domain of the Igusa chart $\mathcal C.\mathrm{CIg}\,\ell$ is carried by the semilinear automorphism $\mathrm{arithmeticGalois}$ of $\tau$ on $\mathrm{fieldBar}\,q\,M'$ (coefficientwise action of $\tau$ on Laurent series) into the domain of $\mathcal C.\mathrm{CIg}\,\ell'$. Only the inclusion of domains is asserted, not any further compatibility of the charts.
--
--   This records the transport along the level automorphisms of the inertia–Igusa anchor at the line $\infty$: inertia at a place above $q$ permutes, up to inclusion of domains, the Igusa components of the mod-$q$ fibre indexed by $\mathbb P^1(\mathbb F_q)$. It supplies the Igusa-domain input to the construction of the linear map on the Tate product in [`ModularCurve.FullLevel.exists_linearMap_tateProd_comp_baseChange_eq_and_eq_zero_of_semistableCovering_of_semistableModel_of_reduction_of_inertiaIgusa`](thm.html#ModularCurve.FullLevel.exists_linearMap_tateProd_comp_baseChange_eq_and_eq_zero_of_semistableCovering_of_semistableModel_of_reduction_of_inertiaIgusa).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_exists_forall_mem_dom_teleChart_eIg_arithmeticGalois_smul_of_inertiaIgusaInftyClause.lean

import Definitions.Def_ModularCurve_FullLevelSemistableCoveringTelescope
import Definitions.Def_ModularCurve_FullLevelSemistableCoveringGuards
import Definitions.Def_ModularCurve_FullLevelSemistableCoveringNaturality
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_DrinfeldCurve_TateRep
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_ModularCurve_FullLevelSemistableCoveringInertiaIgusa

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve IsLocalRing
open scoped TensorProduct

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

theorem ModularCurve.FullLevel.exists_forall_mem_dom_teleChart_eIg_arithmeticGalois_smul_of_inertiaIgusaInftyClause
    (q : ℕ) [Fact q.Prime] (hq : 5 ≤ q) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (lam : ℕ) [Fact lam.Prime] (hqlam : q ≠ lam)
    (hLA : ModularCurve.FullLevel.LevelAutInputs q M') (hGL : ModularCurve.FullLevel.GL2Laws q M')
    (P : ValuationSubring (AlgebraicClosure ℚ)) (hP : P.LiesOverPrime q)
    (W : Finset (AlgebraicCurve.Place (IsLocalRing.ResidueField P)
      (modularFunctionFieldC (IsLocalRing.ResidueField P) M')))
    (hW : ∀ w, w ∈ W ↔ w ∈ ModularCurve.ssPlaces q M' (IsLocalRing.ResidueField P))
    (π : AlgebraicClosure ℚ) (hπ : π ^ (q ^ 2 - 1) = (q : AlgebraicClosure ℚ)) (hπP : π ∈ P)
    (ι : GaloisField q 2 →+* IsLocalRing.ResidueField P)
    [IsDomain (DrinfeldCurve.CoordRing q (IsLocalRing.ResidueField P))]
    (hle : ModularCurve.modularFunctionFieldBar M' ≤ ModularCurve.FullLevel.fieldBar q M')
    (R₀ : AlgebraicCurve.ConstantReduction P ↥(ModularCurve.modularFunctionFieldBar M')
      (modularFunctionFieldC (IsLocalRing.ResidueField P) M'))

    (hR₀ : ∀ (y : LaurentSeries ↥P) (hy : ModularCurve.coeffMap P.subtype y ∈ ModularCurve.modularFunctionFieldBar M'),
      ∃ h : (⟨ModularCurve.coeffMap P.subtype y, hy⟩ : ↥(ModularCurve.modularFunctionFieldBar M')) ∈ R₀.integers,
        ((R₀.residue ⟨_, h⟩ : modularFunctionFieldC (IsLocalRing.ResidueField P) M') :
            LaurentSeries (IsLocalRing.ResidueField P)) =
          ModularCurve.coeffMap (IsLocalRing.residue ↥P) y) :
    letI : Algebra (GaloisField q 2) (IsLocalRing.ResidueField P) := ι.toAlgebra
    ∀ 𝒞 : ModularCurve.FullLevel.SemistableCovering q M' P W,
      𝒞.EquivClauses → 𝒞.W2Clauses π ι q → 𝒞.LevelPinClauses hle R₀ → 𝒞.InertiaClause π →
      𝒞.WidthClause ⟨π, hπP⟩ → 𝒞.GenusClause → 𝒞.DiscFibreClause → 𝒞.CurveClause → 𝒞.NaturalityClauses →
      𝒞.InertiaIgusaInftyClause →
      ∀ τ ∈ P.inertiaSubgroupIn ℚ, ∀ ℓ : CuspidalType.ProjLine q, ∃ ℓ' : CuspidalType.ProjLine q,
        ∀ Q : AlgebraicCurve.Place (AlgebraicClosure ℚ) ↥(ModularCurve.FullLevel.fieldBar q M'), Q ∈ (𝒞.CIg ℓ).dom →
          ModularCurve.arithmeticGalois (ModularCurve.xHFunctionField (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M')) τ • Q ∈
            (𝒞.CIg ℓ').dom := by sorry
