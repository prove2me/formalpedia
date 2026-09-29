-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_exists_linearMap_tateProd_comp_baseChange_eq_and_eq_zero_of_semistableCovering_of_semistableModel_of_inertiaIgusa_of_eq_two
-- name    : ModularCurve.FullLevel.exists_linearMap_tateProd_comp_baseChange_eq_and_eq_zero_of_semistableCovering_of_semistableModel_of_inertiaIgusa_of_eq_two
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:35.562543+00:00
-- url     : https://prove2.me/theorems/5d34c828-6d59-5220-a7df-1891a5dd548a
-- title:
--   Drinfeld specialisation of the λ-adic Tate module, q=2
-- statement:
--   Let $q$ be a prime with $q=2$, let $M'$ be a nonzero natural number with $q \nmid M'$, and let $\lambda$ be a prime different from $q$. Assume `LevelAutInputs q M'` (for every $\zeta$ in `Idx q`, the set of primitive $q$-th roots of unity in $\overline{\mathbb{Q}}$, and every $\gamma \in \Gamma_0(M')$ there is an automorphism of `fieldBar q M'` satisfying the level-automorphism predicate) and `GL2Laws q M'` (a monoid homomorphism $GL_2(\mathbb{Z}/q) \to \operatorname{End}(\mathrm{Jac}\,q\,M')$ inducing `slJac` on $\Gamma_0(M')$ and `diagJac` on diagonal units). Let $P$ be a valuation subring of $\overline{\mathbb{Q}}$ with $q$ a nonunit of $P$, with residue field $\kappa$; let $W$ be the finite set of supersingular places of `modularFunctionFieldC κ M'`; let $\pi \in P$ satisfy $\pi^{q^2-1}=q$; let $\iota : \mathbb{F}_{q^2} \to \kappa$ be a ring homomorphism, and assume [`DrinfeldCurve.CoordRing q κ`](def/DrinfeldCurve_CoordRing.html#L21) is a domain. Let $R_0$ be a constant reduction along $P$ from the base-changed level-$M'$ function field $\overline{F}_{M'} :=$ `modularFunctionFieldBar M'`, which is assumed contained in `fieldBar q M'`, to `modularFunctionFieldC κ M'`, and assume $R_0$ computes coefficientwise reduction: every Laurent series over $P$ whose coefficientwise image in $\overline{\mathbb{Q}}$ lies in $\overline{F}_{M'}$ lies in $R_0$'s ring of integers, and its $R_0$-residue, viewed as a Laurent series over $\kappa$, is the coefficientwise residue of the series. Give $\kappa$ the $\mathbb{F}_{q^2}$-algebra structure from $\iota$. Then for every semistable covering $\mathcal{C}$ of `fieldBar q M'` along $P$ with incidence set $\mathbb{P}^1(\mathbb{F}_q) \times W$ satisfying the equivariance clauses, the Drinfeld clause with an exponent $\eta \in \{1,q\}$ depending on $(\zeta,s)$, the Igusa unipotent clauses, the level-$M'$ pinning clauses for `hle` and $R_0$, the inertia clause for $\pi$, the width clause for $\pi$, the genus, disc-fibre, curve and naturality clauses, and the inertia–Igusa clause at the line at infinity (these clauses summarised here), and for every semistable model $M$ of `fieldBar q M'` over $P$ realising $\mathcal{C}$ (component charts indexed by $\mathbb{P}^1(\mathbb{F}_q) \sqcup W$, annuli indexed by $\mathbb{P}^1(\mathbb{F}_q) \times W$ with source the Igusa end and target the supersingular end, with $\mathcal{C}$'s nodes) and every descent datum $D$ for $M$, there exists a $\mathbb{Q}_\lambda$-linear map $sp_0$ from the rational $\lambda$-adic Tate module of $\mathrm{Jac}\,q\,M'$ to [`DrinfeldCurve.tateProd q κ lam ℚ_[lam] (Idx q × W)`](def/DrinfeldCurve_TateRep.html#L27), that is, to functions on `Idx q × W` with values in $\mathbb{Q}_\lambda \otimes$ (rational $\lambda$-adic Tate module of $\mathrm{Pic}^0$ of the Drinfeld function field over $\kappa$), such that: (i) for every $\tau$ in the inertia subgroup of $P$ over $\mathbb{Q}$, every $\alpha \in \mathbb{F}_{q^2}^\times$ with $\iota(\alpha)$ equal to the tame character of $\tau$ computed with $\pi$, and every $g \in GL_2(\mathbb{Z}/q)$ with $(g,\alpha)$ in `hSubgroup q` (the kernel of $\det \cdot \alpha^{q+1}$), the composite of the base change to $\mathbb{Q}_\lambda$ of `tateGL2 g * tateGal τ` followed by $sp_0$ equals $sp_0$ followed by `tateProdRep` at $\langle (g,\alpha)\rangle$; and (ii) if $v$ in the rational Tate module is annihilated by $\sum_{t \in \mathbb{Z}/q} \mathrm{tateGL2}(u(t)) \cdot \mathrm{tateGL2}(g)$ (base changed) for every $g \in GL_2(\mathbb{Z}/q)$, where $u(t)$ is the upper unipotent matrix with entry $t$, and $sp_0 v = 0$, then $v = 0$.
--
--   This is the arithmetic core of the specialisation of the $\lambda$-adic Tate module of the Jacobian at level $q^2M'$ to the product of Tate modules of the Drinfeld (supersingular) components of the semistable reduction at a place above $q$, in the case $q = 2$: the specialisation map intertwines the combined $GL_2(\mathbb{F}_q)$- and inertia-action with the Drinfeld representation, and is injective on the part of the module killed by the unipotent traces. It is used in the description of the action of inertia at $q$ on the Tate module of the full-level Jacobian, feeding the level-lowering step.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_exists_linearMap_tateProd_comp_baseChange_eq_and_eq_zero_of_semistableCovering_of_semistableModel_of_inertiaIgusa_of_eq_two.lean

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

theorem ModularCurve.FullLevel.exists_linearMap_tateProd_comp_baseChange_eq_and_eq_zero_of_semistableCovering_of_semistableModel_of_inertiaIgusa_of_eq_two
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
