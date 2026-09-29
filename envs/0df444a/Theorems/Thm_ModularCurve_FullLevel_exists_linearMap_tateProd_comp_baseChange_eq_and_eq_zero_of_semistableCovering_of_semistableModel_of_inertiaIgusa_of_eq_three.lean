-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_exists_linearMap_tateProd_comp_baseChange_eq_and_eq_zero_of_semistableCovering_of_semistableModel_of_inertiaIgusa_of_eq_three
-- name    : ModularCurve.FullLevel.exists_linearMap_tateProd_comp_baseChange_eq_and_eq_zero_of_semistableCovering_of_semistableModel_of_inertiaIgusa_of_eq_three
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:35.562543+00:00
-- url     : https://prove2.me/theorems/fa12b12f-d483-515b-8044-cdc0b8776b97
-- title:
--   Tate-module specialisation from a semistable covering, q=3
-- statement:
--   Let $q$ be a prime with $q=3$, let $M'\ge 1$ with $q\nmid M'$, and let $\lambda$ be a prime with $\lambda\neq q$. Assume `LevelAutInputs q M'` (for each primitive $q$-th root of unity $\zeta$ in $\overline{\mathbb{Q}}$, indexed by `Idx q`, and each $\gamma\in\Gamma_0(M')$ a level automorphism of `fieldBar q M'` over $\overline{\mathbb{Q}}$ exists) and `GL2Laws q M'` (a monoid map $GL_2(\mathbb{F}_q)\to\mathrm{End}(\mathrm{Jac}\,q\,M')$ matching `slJac` on reductions of $\Gamma_0(M')$ and `diagJac` on the elements `diagOneElem`). Let $P$ be a valuation subring of $\overline{\mathbb{Q}}$ with $q$ a nonunit in $P$, residue field $\kappa$; let $W$ be the finset of places of `modularFunctionFieldC κ M'` consisting exactly of the supersingular places `ssPlaces q M' κ`; let $\pi\in P$ satisfy $\pi^{q^2-1}=q$; let $\iota:\mathbb{F}_{q^2}\to\kappa$ be a ring map, making `CoordRing q κ` a domain; let `modularFunctionFieldBar M' ≤ fieldBar q M'`, and let $R_0$ be a constant reduction of the level-$M'$ field to `modularFunctionFieldC κ M'` whose residue map computes coefficientwise reduction of Laurent series over $P$. Then for every semistable covering $\mathcal{C}$ of `fieldBar q M'` along $P$ with supersingular index set $W$ satisfying the clauses `EquivClauses`, a Drinfeld clause `DrinfeldClause π ι η ζ s` with exponent $\eta\in\{1,q\}$ depending on $(\zeta,s)$, `IgusaUnipotentClause`, `LevelPinClauses hle R₀`, `InertiaClause π`, `WidthClause`, `GenusClause`, `DiscFibreClause`, `CurveClause`, `NaturalityClauses` and `InertiaIgusaInftyClause` (summarised here), and for every semistable model $M$ of `fieldBar q M'` over $P$ whose components are indexed by $\mathbb{P}^1(\mathbb{F}_q)\sqcup W$ through $\mathcal{C}$'s charts and whose annuli are $\mathcal{C}.An$ indexed by $\mathbb{P}^1(\mathbb{F}_q)\times W$ with the stated sources, targets and node places, and every descent datum $D$ for $M$, there is a $\mathbb{Q}_\lambda$-linear map $sp_0$ from the rational $\lambda$-adic Tate module of $\mathrm{Jac}\,q\,M'$ to `tateProd q κ lam ℚ_[lam] (Idx q × W)`, i.e. to functions on `Idx q × W` with values in $\mathbb{Q}_\lambda\otimes$ the rational Tate module of $\mathrm{Pic}^0$ of the Drinfeld function field over $\kappa$, such that: (i) for every $\tau$ in the inertia subgroup of $P$ over $\mathbb{Q}$, every $\alpha\in\mathbb{F}_{q^2}^\times$ with $\iota(\alpha)$ the tame character of $\tau$ relative to $\pi$, and every $g\in GL_2(\mathbb{F}_q)$ with $(g,\alpha)$ in `hSubgroup q`, the base change of `tateGL2 g * tateGal τ` followed by $sp_0$ equals $sp_0$ followed by `tateProdRep ⟨(g,α),hg⟩`; and (ii) any $v$ annihilated by $\bigl(\sum_{t\in\mathbb{Z}/q}\mathrm{tateGL2}(\mathrm{unipotent}\,t)\bigr)\cdot\mathrm{tateGL2}(g)$ (base changed) for all $g\in GL_2(\mathbb{F}_q)$ and satisfying $sp_0v=0$ is zero.
--
--   This is the arithmetic core of the specialisation step: from a semistable covering of the full-level modular function field at a place above $q$, together with a semistable model and a descent datum, it produces a $GL_2(\mathbb{F}_q)\times$inertia-equivariant map from the $\lambda$-adic Tate module of the full-level Jacobian to a product of Tate modules of Drinfeld-curve Jacobians, injective on the part killed by the unipotent-sum operators. It is the $q=3$ instance, with the `InertiaIgusaInftyClause` anchor, and is used by [`FullLevelTate.exists_linearMap_tateProd_comp_baseChange_eq_and_eq_zero_of_eq_three_of_dvd`](thm.html#FullLevelTate.exists_linearMap_tateProd_comp_baseChange_eq_and_eq_zero_of_eq_three_of_dvd).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_exists_linearMap_tateProd_comp_baseChange_eq_and_eq_zero_of_semistableCovering_of_semistableModel_of_inertiaIgusa_of_eq_three.lean

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

theorem ModularCurve.FullLevel.exists_linearMap_tateProd_comp_baseChange_eq_and_eq_zero_of_semistableCovering_of_semistableModel_of_inertiaIgusa_of_eq_three
    (q : ℕ) [Fact q.Prime] (hq3 : q = 3) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
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
