-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_exists_linearMap_rationalTateModule_drinfeld_injective_comp_eq_of_inducesOnChart_of_semistableCovering_of_eq_two
-- name    : ModularCurve.FullLevel.exists_linearMap_rationalTateModule_drinfeld_injective_comp_eq_of_inducesOnChart_of_semistableCovering_of_eq_two
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:35.562543+00:00
-- url     : https://prove2.me/theorems/3fc3518e-d9a3-5307-865f-2a0d9253e03e
-- title:
--   Drinfeld identification on supersingular charts at q=2
-- statement:
--   Let $q$ be a prime with $q=2$, let $M'$ be a nonzero natural number with $q \nmid M'$, and let $\lambda$ be a prime with $q \neq \lambda$. Assume `LevelAutInputs q M'`, namely that for each $\zeta$ in `Idx q` (the primitive $q$-th roots of unity in $\overline{\mathbb{Q}}$) and each $\gamma \in \Gamma_0(M') \subseteq SL_2(\mathbb{Z})$ a level automorphism of `fieldBar q M'` — the base change to $\overline{\mathbb{Q}}$ of the function field of $X_H(q^2M')$ for $H$ the kernel of $(\mathbb{Z}/q^2M')^\times \to (\mathbb{Z}/q)^\times$ — exists in the sense of `IsLevelAutBar`, and assume `GL2Laws q M'`, namely that the Hecke-module actions `slJac` of $\Gamma_0(M')$ and `diagJac` of the diagonal units on the Jacobian `Jac q M'` come from a single homomorphism $GL_2(\mathbb{Z}/q) \to \operatorname{End}(\mathrm{Jac})$ via `redQ` and `diagOneElem`. Let $P$ be a valuation subring of $\overline{\mathbb{Q}}$ with $q$ a non-unit of $P$, let $W$ be a finite set of places of `modularFunctionFieldC` over $\kappa(P) =$ the residue field of $P$ whose members are exactly the supersingular places `ssPlaces q M'`, let $\pi \in P$ satisfy $\pi^{q^2-1} = q$, let $\iota : \mathbb{F}_{q^2} \to \kappa(P)$ be a ring homomorphism, and assume the Drinfeld coordinate ring [`DrinfeldCurve.CoordRing q κ(P)`](def/DrinfeldCurve_CoordRing.html#L21) is a domain. Let $hle$ witness `modularFunctionFieldBar M' ≤ fieldBar q M'`, and let $R_0$ be a constant reduction of `modularFunctionFieldBar M'` along $P$ with values in `modularFunctionFieldC κ(P) M'`, compatible with coefficientwise reduction of Laurent series: every Laurent series $y$ over $P$ whose coefficientwise image lies in `modularFunctionFieldBar M'` lies in $R_0$'s integers and has $R_0$-residue equal, as a Laurent series over $\kappa(P)$, to the coefficientwise reduction of $y$. Give $\kappa(P)$ the $\mathbb{F}_{q^2}$-algebra structure from $\iota$. Then for every semistable covering $\mathcal{C}$ of `fieldBar q M'` along $P$ with supersingular index set $W$ satisfying the clauses `EquivClauses`, `IgusaUnipotentClause` for every $\zeta$, `LevelPinClauses hle R₀`, `InertiaClause π`, `WidthClause ⟨π, hπP⟩`, `GenusClause`, `DiscFibreClause`, `CurveClause` and `NaturalityClauses`, and such that for each $\zeta$ and each $s \in W$ there is $\eta \in \{1, q\}$ with `𝒞.DrinfeldClause π ι η ζ s` (an identification of the supersingular chart field $\mathcal{C}.FSS\,s$ with the fixed field of a subgroup of the $(q+1)$-st roots of unity in the Drinfeld function field, intertwining level automorphisms with the action of $(\gamma \bmod q, 1)$ and tame inertia of value $\iota(\alpha)$ with that of $(\mathrm{diag}(1,d^{\eta})^{-1}, \alpha^{\eta})$), there is a family of $\mathbb{Q}_\lambda$-linear maps $\Phi_{\zeta,s}$ from the rational $\lambda$-adic Tate module $\mathbb{Q}_\lambda \otimes_{\mathbb{Z}_\lambda} T_\lambda$ of $\mathrm{Pic}^0$ of the telescoped chart field $\mathcal{C}.teleFbar(\mathcal{C}.eSS\,s)$ over $\kappa(P)$ to that of $\mathrm{Pic}^0$ of the Drinfeld function field over $\kappa(P)$, such that: each $\Phi_{\zeta,s}$ is injective; for $\gamma \in \Gamma_0(M')$ and every $\kappa(P)$-algebra automorphism $\varphi$ of $\mathcal{C}.teleFbar(\mathcal{C}.eSS\,s)$ inducing on the chart $\mathcal{C}.teleChart(\mathcal{C}.eSS\,s)$ the semilinear automorphism attached to `levelAutBar q M' ζ γ⁻¹` (the chart integers are preserved and the chart residue map intertwines the two), and for every proof that $(\mathrm{redQ}(\gamma), 1)$ lies in `hSubgroup q`, one has $\Phi_{\zeta,s} \circ \rho_\lambda(\varphi) = \rho_\lambda(\mathrm{hFunctionFieldAction}(\mathrm{redQ}(\gamma),1)) \circ \Phi_{\zeta,s}$, where $\rho_\lambda$ denotes the rational Tate-module representation of the relevant automorphism group; and for every $\tau$ in the inertia subgroup of $P$ over $\mathbb{Q}$, every unit $\alpha$ of $\mathbb{F}_{q^2}$ with $\iota(\alpha) =$ `P.tameCharacter π τ`, every $\varphi$ inducing on that chart the semilinear automorphism `arithmeticGalois (xHFunctionField (q^2*M') (levelH q M')) τ`, and every unit $e$ of $\mathbb{Z}/q$ with $(\mathrm{diagOneElem}(e), \alpha) \in$ `hSubgroup q` (a condition which forces $e$ to be the image of $\alpha^{-(q+1)}$), one has $\Phi_{\zeta,s} \circ \rho_\lambda(\varphi) = \rho_\lambda(\mathrm{hFunctionFieldAction}(\mathrm{diagOneElem}(e), \alpha)) \circ \Phi_{\zeta,s}$.
--
--   This is the Drinfeld (Deligne–Lusztig) identification of the supersingular part of the reduction of the full-level modular curve at $q$, recast as an injective map of rational $\lambda$-adic Tate modules of Jacobians that intertwines the level automorphisms coming from $\Gamma_0(M')$ and the action of tame inertia at $q$ with the corresponding actions on the Drinfeld curve; here $q = 2$, where the exponent in the inertia part of the Drinfeld clause is only pinned up to $\eta \in \{1,q\}$. It feeds the arithmetic computation of the local behaviour at $q$ of the $\lambda$-adic representation attached to the full-level Jacobian, supplying the intertwining maps required by [`ModularCurve.FullLevel.exists_linearMap_tateProd_comp_baseChange_eq_and_eq_zero_of_semistableCovering_of_semistableModel_of_reduction_of_inertiaIgusa_of_eq_two`](thm.html#ModularCurve.FullLevel.exists_linearMap_tateProd_comp_baseChange_eq_and_eq_zero_of_semistableCovering_of_semistableModel_of_reduction_of_inertiaIgusa_of_eq_two).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_exists_linearMap_rationalTateModule_drinfeld_injective_comp_eq_of_inducesOnChart_of_semistableCovering_of_eq_two.lean

import Definitions.Def_ModularCurve_FullLevelSemistableCoveringTelescope
import Definitions.Def_ModularCurve_FullLevelSemistableCoveringGuards
import Definitions.Def_ModularCurve_FullLevelSemistableCoveringNaturality
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_DrinfeldCurve_TateRep
import Definitions.Def_AlgebraicCurve_IsCurveOver

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve IsLocalRing
open scoped TensorProduct

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

theorem ModularCurve.FullLevel.exists_linearMap_rationalTateModule_drinfeld_injective_comp_eq_of_inducesOnChart_of_semistableCovering_of_eq_two
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
      ∃ Φ : (ζ : ModularCurve.FullLevel.Idx q) → (s : ↥W) →
          (ModularCurve.RationalTateModule lam (Pic0 (IsLocalRing.ResidueField P) (𝒞.teleFbar (𝒞.eSS s))) →ₗ[ℚ_[lam]]
            ModularCurve.RationalTateModule lam
              (Pic0 (IsLocalRing.ResidueField P)
                (DrinfeldCurve.drinfeldFunctionField q (IsLocalRing.ResidueField P)))),
        (∀ (ζ : ModularCurve.FullLevel.Idx q) (s : ↥W), Function.Injective (Φ ζ s)) ∧
        (∀ (ζ : ModularCurve.FullLevel.Idx q) (s : ↥W) (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ),
          γ ∈ CongruenceSubgroup.Gamma0 M' →
          ∀ φ : 𝒞.teleFbar (𝒞.eSS s) ≃ₐ[IsLocalRing.ResidueField P] 𝒞.teleFbar (𝒞.eSS s),
            ModularCurve.FullLevel.SemistableCovering.InducesOnChart (𝒞.teleChart (𝒞.eSS s))
                (SemilinearAut.ofAlgAut (ModularCurve.FullLevel.levelAutBar q M' ζ γ⁻¹)) φ.toRingEquiv →
            ∀ hmem : (ModularCurve.FullLevel.redQ q γ, (1 : (GaloisField q 2)ˣ)) ∈ DrinfeldCurve.hSubgroup q,
              Φ ζ s ∘ₗ ModularCurve.rationalGaloisRep lam (Pic0 (IsLocalRing.ResidueField P) (𝒞.teleFbar (𝒞.eSS s)))
                (𝒞.teleFbar (𝒞.eSS s) ≃ₐ[IsLocalRing.ResidueField P] 𝒞.teleFbar (𝒞.eSS s)) φ =
              ModularCurve.rationalGaloisRep lam
                (Pic0 (IsLocalRing.ResidueField P) (DrinfeldCurve.drinfeldFunctionField q (IsLocalRing.ResidueField P)))
                (DrinfeldCurve.drinfeldFunctionField q (IsLocalRing.ResidueField P) ≃ₐ[IsLocalRing.ResidueField P]
                  DrinfeldCurve.drinfeldFunctionField q (IsLocalRing.ResidueField P))
                (DrinfeldCurve.hFunctionFieldAction q (IsLocalRing.ResidueField P) ⟨_, hmem⟩) ∘ₗ Φ ζ s) ∧
        (∀ (ζ : ModularCurve.FullLevel.Idx q) (s : ↥W), ∀ τ ∈ P.inertiaSubgroupIn ℚ, ∀ α : (GaloisField q 2)ˣ,
          ι (α : GaloisField q 2) = P.tameCharacter π τ →
          ∀ φ : 𝒞.teleFbar (𝒞.eSS s) ≃ₐ[IsLocalRing.ResidueField P] 𝒞.teleFbar (𝒞.eSS s),
            ModularCurve.FullLevel.SemistableCovering.InducesOnChart (𝒞.teleChart (𝒞.eSS s))
                (ModularCurve.arithmeticGalois
                  (ModularCurve.xHFunctionField (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M')) τ) φ.toRingEquiv →
            ∀ (e : (ZMod q)ˣ) (hmem : (ModularCurve.FullLevel.diagOneElem q e, α) ∈ DrinfeldCurve.hSubgroup q),
              Φ ζ s ∘ₗ ModularCurve.rationalGaloisRep lam (Pic0 (IsLocalRing.ResidueField P) (𝒞.teleFbar (𝒞.eSS s)))
                (𝒞.teleFbar (𝒞.eSS s) ≃ₐ[IsLocalRing.ResidueField P] 𝒞.teleFbar (𝒞.eSS s)) φ =
              ModularCurve.rationalGaloisRep lam
                (Pic0 (IsLocalRing.ResidueField P) (DrinfeldCurve.drinfeldFunctionField q (IsLocalRing.ResidueField P)))
                (DrinfeldCurve.drinfeldFunctionField q (IsLocalRing.ResidueField P) ≃ₐ[IsLocalRing.ResidueField P]
                  DrinfeldCurve.drinfeldFunctionField q (IsLocalRing.ResidueField P))
                (DrinfeldCurve.hFunctionFieldAction q (IsLocalRing.ResidueField P) ⟨_, hmem⟩) ∘ₗ Φ ζ s) := by sorry
