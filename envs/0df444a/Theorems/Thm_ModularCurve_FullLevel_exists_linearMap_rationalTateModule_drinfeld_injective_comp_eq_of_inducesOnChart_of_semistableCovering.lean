-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_exists_linearMap_rationalTateModule_drinfeld_injective_comp_eq_of_inducesOnChart_of_semistableCovering
-- name    : ModularCurve.FullLevel.exists_linearMap_rationalTateModule_drinfeld_injective_comp_eq_of_inducesOnChart_of_semistableCovering
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:35.562543+00:00
-- url     : https://prove2.me/theorems/da70a2c8-ab90-5cda-9915-ba6ba8c8c593
-- title:
--   Drinfeld intertwining on the supersingular charts, rational Tate modules
-- statement:
--   Fix a prime $q\ge 5$, a positive integer $M'$ with $q\nmid M'$, and a prime $\lambda\ne q$. Assume `LevelAutInputs q M'`, i.e. for each $\zeta$ in `Idx q` (the primitive $q$-th roots of unity in $\overline{\mathbb Q}$) and each $\gamma\in\Gamma_0(M')$ a level automorphism of `fieldBar q M'` exists, and `GL2Laws q M'`, i.e. there is a monoid homomorphism from $GL_2(\mathbb Z/q)$ to $\mathrm{End}(\mathrm{Jac}\,q\,M')$ matching `slJac` on reductions of $\Gamma_0(M')$-matrices and `diagJac` on the elements $\mathrm{diag}(1,d)$. Let $P$ be a valuation subring of $\overline{\mathbb Q}$ in which $q$ is a non-unit, $W$ a finite set of places of `modularFunctionFieldC (ResidueField P) M'` consisting exactly of the supersingular places `ssPlaces q M'`, $\pi\in P$ with $\pi^{q^2-1}=q$, $\iota:\mathbb F_{q^2}\to\kappa(P)$ a ring homomorphism (used as the algebra structure on $\kappa(P)$), the Drinfeld coordinate ring [`DrinfeldCurve.CoordRing q (ResidueField P)`](def/DrinfeldCurve_CoordRing.html#L21) a domain, `modularFunctionFieldBar M' ≤ fieldBar q M'` via `hle`, and $R_0$ a `ConstantReduction` of `modularFunctionFieldBar M'` to `modularFunctionFieldC (ResidueField P) M'` whose residue map computes coefficientwise reduction of Laurent series over $P$ (hypothesis `hR₀`). Then for every semistable covering $\mathcal C$ of `fieldBar q M'` along $P$ with supersingular index set $W$ satisfying the nine clauses `EquivClauses`, `W2Clauses π ι q`, `LevelPinClauses hle R₀`, `InertiaClause π`, `WidthClause ⟨π, hπP⟩`, `GenusClause`, `DiscFibreClause`, `CurveClause` and `NaturalityClauses`, there is a family of $\mathbb Q_\lambda$-linear maps
--   $$\Phi_{\zeta,s}:\;V_\lambda\bigl(\mathrm{Pic}^0(\mathcal C.\mathrm{teleFbar}(\mathcal C.\mathrm{eSS}\,s))\bigr)\longrightarrow V_\lambda\bigl(\mathrm{Pic}^0(\text{Drinfeld function field over }\kappa(P))\bigr),$$
--   indexed by $\zeta$ in `Idx q` and $s\in W$, each injective, with two intertwining properties. First, for $\gamma\in SL_2(\mathbb Z)\cap\Gamma_0(M')$ and any $\kappa(P)$-automorphism $\varphi$ of the chart field which induces on `teleChart (eSS s)` the semilinear automorphism attached to `levelAutBar q M' ζ γ⁻¹` (membership in the chart's integers is preserved and the chart residue of the translate is $\varphi$ of the residue), and for any witness that $(\mathrm{redQ}\,q\,\gamma,1)$ lies in `hSubgroup q`, the composite of $\Phi_{\zeta,s}$ with the rational Galois representation of $\varphi$ equals the composite of the rational Galois representation of `hFunctionFieldAction` at that pair with $\Phi_{\zeta,s}$. Second, for $\tau$ in the inertia subgroup of $P$ over $\mathbb Q$ and $\alpha\in\mathbb F_{q^2}^\times$ with $\iota(\alpha)=$ `P.tameCharacter π τ`, for any $\varphi$ inducing on the same chart the semilinear automorphism `arithmeticGalois (xHFunctionField (q^2*M') (levelH q M')) τ`, and for every $e\in(\mathbb Z/q)^\times$ together with a witness that $(\mathrm{diagOneElem}\,q\,e,\alpha)\in$ `hSubgroup q`, the same intertwining holds with the Drinfeld action of that pair.
--
--   This is the Drinfeld identification of the supersingular charts of a semistable covering of the full-level modular curve, transported to $\lambda$-adic rational Tate modules of the Jacobians, where the level automorphisms of $\Gamma_0(M')$ and tame inertia are matched with the action of the subgroup $H\subset GL_2(\mathbb F_q)\times\mathbb F_{q^2}^\times$ on the Drinfeld curve. It supplies the injective-map hypothesis used by the per-factor assembly of the $\lambda$-adic representation, [`ModularCurve.FullLevel.exists_linearMap_tateProd_comp_baseChange_eq_and_eq_zero_of_semistableCovering_of_semistableModel_of_reduction_of_inertiaIgusa`](thm.html#ModularCurve.FullLevel.exists_linearMap_tateProd_comp_baseChange_eq_and_eq_zero_of_semistableCovering_of_semistableModel_of_reduction_of_inertiaIgusa).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_exists_linearMap_rationalTateModule_drinfeld_injective_comp_eq_of_inducesOnChart_of_semistableCovering.lean

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

theorem ModularCurve.FullLevel.exists_linearMap_rationalTateModule_drinfeld_injective_comp_eq_of_inducesOnChart_of_semistableCovering
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
