-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_exists_linearMap_tateProd_comp_baseChange_eq_and_eq_zero_of_semistableCovering_of_semistableModel_of_inertiaIgusa
-- name    : ModularCurve.FullLevel.exists_linearMap_tateProd_comp_baseChange_eq_and_eq_zero_of_semistableCovering_of_semistableModel_of_inertiaIgusa
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:35.562543+00:00
-- url     : https://prove2.me/theorems/3092066d-f950-582a-aec1-1a2a191e109e
-- title:
--   Drinfeld specialisation of the full-level Tate module
-- statement:
--   Fix a prime $q \ge 5$, a nonzero $M'$ with $q \nmid M'$, and a prime $\lambda \ne q$; assume `LevelAutInputs q M'` (every pair consisting of a primitive $q$-th root of unity $\zeta$ and $\gamma \in \Gamma_0(M')$ is realised by an automorphism of `fieldBar q M'` satisfying `IsLevelAutBar`) and `GL2Laws q M'` (a monoid map $GL_2(\mathbb{Z}/q) \to \operatorname{End}(\mathrm{Jac}\,q\,M')$ compatible with the $\Gamma_0(M')$-action and with diagonal elements). Let $P$ be a valuation subring of $\overline{\mathbb{Q}}$ in which $q$ is a nonunit, $W$ the finite set of places of $\mathrm{modularFunctionFieldC}$ over the residue field $k_P$ consisting exactly of the supersingular places for $q, M'$, $\pi \in P$ with $\pi^{q^2-1} = q$, and $\iota : \mathbb{F}_{q^2} \to k_P$ a ring homomorphism, the Drinfeld coordinate ring over $k_P$ being a domain. Let $\mathrm{hle}$ witness $\mathrm{modularFunctionFieldBar}\,M' \le \mathrm{fieldBar}\,q\,M'$, and let $R_0$ be a constant reduction of $\mathrm{modularFunctionFieldBar}\,M'$ to $\mathrm{modularFunctionFieldC}\,k_P\,M'$ over $P$ whose residue computes, on Laurent series with coefficients in $P$, the coefficientwise reduction. Then for every semistable covering $\mathcal{C}$ of $\mathrm{fieldBar}\,q\,M'$ over $P$ with node data indexed by $W$, satisfying the ten clauses `EquivClauses`, `W2Clauses π ι q`, `LevelPinClauses hle R₀`, `InertiaClause π`, `WidthClause ⟨π, hπP⟩`, `GenusClause`, `DiscFibreClause`, `CurveClause`, `NaturalityClauses` and `InertiaIgusaInftyClause` (summarised here), and for every semistable model $M$ over $P$ built from the charts $\mathcal{C}.\mathrm{sumChart}$, the annuli $\mathcal{C}.An$ and the node places $\mathcal{C}.\mathrm{sumNode}$, and every descent $D$ of $M$, there is a $\mathbb{Q}_\lambda$-linear map $sp_0$ from the rational Tate module $V_\lambda(\mathrm{Jac}\,q\,M')$ to the product, indexed by $\mathrm{Idx}\,q \times W$, of the rational Tate modules of $\mathrm{Pic}^0$ of the Drinfeld function field over $k_P$, such that: (i) for every $\tau$ in the inertia subgroup of $P$ over $\mathbb{Q}$, every $\alpha \in \mathbb{F}_{q^2}^\times$ with $\iota(\alpha)$ equal to the tame character value $P.\mathrm{tameCharacter}\,\pi\,\tau$, and every $g \in GL_2(\mathbb{Z}/q)$ with $(g,\alpha)$ in the kernel `hSubgroup` of the character $\det(g)\cdot\alpha^{q+1}$, the composite of the base change of $\mathrm{tateGL2}(g)\,\mathrm{tateGal}(\tau)$ followed by $sp_0$ equals $sp_0$ followed by $\mathrm{tateProdRep}$ at $\langle (g,\alpha), hg\rangle$; and (ii) if $v$ is annihilated by $\sum_{t \in \mathbb{Z}/q} \mathrm{tateGL2}(\mathrm{unipotent}\,t)\,\mathrm{tateGL2}(g)$ for every $g$, and $sp_0 v = 0$, then $v = 0$.
--
--   This is the covering-level arithmetic reduction step: it produces, from a semistable covering of the full-level modular curve together with a semistable model and a descent of it, the specialisation map comparing the $\lambda$-adic Tate module of the full-level Jacobian with the Tate modules of the Drinfeld curve attached to the supersingular points, equivariantly for $GL_2(\mathbb{Z}/q)$ and for inertia at $q$ through the tame character, and injectively on the part cut out by the unipotent trace operators. The present edition carries the inertia–Igusa anchor clause `InertiaIgusaInftyClause` for the component at the point $\infty$ of the projective line, and feeds the full-level Tate-module statement [`FullLevelTate.exists_linearMap_tateProd_comp_baseChange_eq_and_eq_zero_of_five_le`](thm.html#FullLevelTate.exists_linearMap_tateProd_comp_baseChange_eq_and_eq_zero_of_five_le).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_exists_linearMap_tateProd_comp_baseChange_eq_and_eq_zero_of_semistableCovering_of_semistableModel_of_inertiaIgusa.lean

import Definitions.Def_ModularCurve_FullLevelSemistableCoveringGuards
import Definitions.Def_ModularCurve_FullLevelSemistableCoveringNaturality
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_DrinfeldCurve_TateRep
import Definitions.Def_ModularCurve_FullLevelSemistableCoveringTelescope
import Definitions.Def_AlgebraicCurve_SemistableModel
import Definitions.Def_ModularCurve_FullLevelSemistableCoveringInertiaIgusa

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsLocalRing
open AlgebraicCurve
open scoped TensorProduct

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

theorem ModularCurve.FullLevel.exists_linearMap_tateProd_comp_baseChange_eq_and_eq_zero_of_semistableCovering_of_semistableModel_of_inertiaIgusa
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
      ∀ (M : AlgebraicCurve.SemistableModel P ↥(ModularCurve.FullLevel.fieldBar q M') 𝒞.sumFbar 𝒞.sumChart
          (fun e : CuspidalType.ProjLine q × ↥W => 𝒞.An e.1 e.2)
          (fun e => Sum.inl e.1) (fun e => Sum.inr e.2)
          (fun e => 𝒞.sumNode (Sum.inl e.1) e) (fun e => 𝒞.sumNode (Sum.inr e.2) e))
        (D : M.Descent),
      ∃ sp₀ : ModularCurve.RationalTateModule lam (ModularCurve.FullLevel.Jac q M') →ₗ[ℚ_[lam]]
          DrinfeldCurve.tateProd q (IsLocalRing.ResidueField P) lam ℚ_[lam] (ModularCurve.FullLevel.Idx q × ↥W),
        (∀ τ ∈ P.inertiaSubgroupIn ℚ, ∀ α : (GaloisField q 2)ˣ,
          ι (α : GaloisField q 2) = P.tameCharacter π τ →
            ∀ (g : CuspidalType.GL2 q) (hg : (g, α) ∈ DrinfeldCurve.hSubgroup q),
              sp₀ ∘ₗ (ModularCurve.FullLevel.tateGL2 q M' lam g *
                  ModularCurve.FullLevel.tateGal q M' lam τ).baseChange ℚ_[lam] =
                DrinfeldCurve.tateProdRep q (IsLocalRing.ResidueField P) lam ℚ_[lam]
                  (ModularCurve.FullLevel.Idx q × ↥W) ⟨(g, α), hg⟩ ∘ₗ sp₀) ∧
        (∀ v : ModularCurve.RationalTateModule lam (ModularCurve.FullLevel.Jac q M'),
          (∀ g : CuspidalType.GL2 q,
            (∑ t : ZMod q,
              (ModularCurve.FullLevel.tateGL2 q M' lam (CuspidalType.unipotent q t)).baseChange ℚ_[lam] *
                (ModularCurve.FullLevel.tateGL2 q M' lam g).baseChange ℚ_[lam]) v = 0) →
          sp₀ v = 0 → v = 0) := by sorry
