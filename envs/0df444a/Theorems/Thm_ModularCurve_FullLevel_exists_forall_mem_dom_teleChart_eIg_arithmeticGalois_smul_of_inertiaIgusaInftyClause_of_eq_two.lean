-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_exists_forall_mem_dom_teleChart_eIg_arithmeticGalois_smul_of_inertiaIgusaInftyClause_of_eq_two
-- name    : ModularCurve.FullLevel.exists_forall_mem_dom_teleChart_eIg_arithmeticGalois_smul_of_inertiaIgusaInftyClause_of_eq_two
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:33.630704+00:00
-- url     : https://prove2.me/theorems/ec73c355-905b-57ad-b51f-dc5f107e58f2
-- title:
--   Inertia transports Igusa chart domains, case q=2
-- statement:
--   Let $q$ be a prime with $q=2$, let $M'$ be a non-zero natural number not divisible by $q$, and let $\mathrm{lam}$ be a prime different from $q$. Assume the level-automorphism input condition `LevelAutInputs q M'` (for each primitive $q$-th root of unity $\zeta$ in $\overline{\mathbb Q}$ and each $\gamma\in\Gamma_0(M')$ an automorphism of `fieldBar q M'` realising the prescribed $q$-expansion law exists) and the condition `GL2Laws q M'` (a monoid map from $GL_2(\mathbb Z/q)$ to endomorphisms of the Jacobian matching `slJac` on reductions of $\Gamma_0(M')$ and `diagJac` on the diagonal elements). Let $P$ be a valuation subring of $\overline{\mathbb Q}$ with $q$ a non-unit of $P$, let $W$ be a finite set of places of `modularFunctionFieldC (ResidueField P) M'` whose members are exactly the supersingular places `ssPlaces q M'`, let $\pi\in P$ satisfy $\pi^{q^2-1}=q$, and let $\iota\colon \mathbb F_{q^2}\to \mathrm{ResidueField}\,P$ be a ring homomorphism, the Drinfeld coordinate ring over the residue field being a domain. Let `hle` witness `modularFunctionFieldBar M' ≤ fieldBar q M'`, and let $R_0$ be a constant reduction of `modularFunctionFieldBar M'` to `modularFunctionFieldC (ResidueField P) M'` along $P$ which is compatible with coefficientwise reduction: for every Laurent series $y$ over $P$ whose coefficientwise image lies in `modularFunctionFieldBar M'`, that image lies in $R_0$'s integers and its $R_0$-residue, read as a Laurent series over the residue field, is the coefficientwise reduction of $y$. Then, with `ResidueField P` an $\mathbb F_{q^2}$-algebra via $\iota$, for every semistable covering $\mathcal C$ of type `SemistableCovering q M' P W` satisfying the equivalence clauses, a hedged Drinfeld clause (for each index $\zeta$ and each $s\in W$ there is $\eta\in\{1,q\}$ with `𝒞.DrinfeldClause π ι η ζ s`), the Igusa unipotent clause for every index, the level-pin clauses for `hle` and $R_0$, the inertia clause for $\pi$, the width clause for $\pi$, the genus, disc-fibre, curve and naturality clauses, and the inertia–Igusa clause at $\infty$: for every $\tau$ in the inertia subgroup of $P$ over $\mathbb Q$ and every line $\ell\in\mathbb P^1(\mathbb Z/q)$ there is a line $\ell'$ such that every place $Q$ of `fieldBar q M'` over $\overline{\mathbb Q}$ lying in the domain of the chart $\mathcal C.\mathrm{CIg}\,\ell$ has its image under the semilinear automorphism [`ModularCurve.arithmeticGalois (xHFunctionField (q ^ 2 * M') (levelH q M')) τ`](def/ModularCurve_ArithmeticGalois.html#L54) in the domain of $\mathcal C.\mathrm{CIg}\,\ell'$.
--
--   This is the $q=2$ instance of the transport of the inertia–Igusa anchor at the cusp $\infty$ along the level automorphisms: the anchoring clause fixes the domain of the Igusa chart indexed by the line at infinity, and the naturality clauses together with the covariance of the level automorphisms under the Galois action propagate the statement to every line of $\mathbb P^1(\mathbb Z/q)$, the conclusion being independent of the hedged Drinfeld exponent. It feeds the computation of the inertia action on the Tate-product part of the semistable model at level $q^2M'$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_exists_forall_mem_dom_teleChart_eIg_arithmeticGalois_smul_of_inertiaIgusaInftyClause_of_eq_two.lean

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

theorem ModularCurve.FullLevel.exists_forall_mem_dom_teleChart_eIg_arithmeticGalois_smul_of_inertiaIgusaInftyClause_of_eq_two
    (q : ℕ) [Fact q.Prime] (hq2 : q = 2) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
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
      𝒞.EquivClauses →
      (∀ (ζ : ModularCurve.FullLevel.Idx q) (s : ↥W), ∃ η : ℕ, (η = 1 ∨ η = q) ∧ 𝒞.DrinfeldClause π ι η ζ s) →
      (∀ ζ : ModularCurve.FullLevel.Idx q, 𝒞.IgusaUnipotentClause ζ) → 𝒞.LevelPinClauses hle R₀ → 𝒞.InertiaClause π →
      𝒞.WidthClause ⟨π, hπP⟩ → 𝒞.GenusClause → 𝒞.DiscFibreClause → 𝒞.CurveClause → 𝒞.NaturalityClauses →
      𝒞.InertiaIgusaInftyClause →
      ∀ τ ∈ P.inertiaSubgroupIn ℚ, ∀ ℓ : CuspidalType.ProjLine q, ∃ ℓ' : CuspidalType.ProjLine q,
        ∀ Q : AlgebraicCurve.Place (AlgebraicClosure ℚ) ↥(ModularCurve.FullLevel.fieldBar q M'), Q ∈ (𝒞.CIg ℓ).dom →
          ModularCurve.arithmeticGalois (ModularCurve.xHFunctionField (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M')) τ • Q ∈
            (𝒞.CIg ℓ').dom := by sorry
