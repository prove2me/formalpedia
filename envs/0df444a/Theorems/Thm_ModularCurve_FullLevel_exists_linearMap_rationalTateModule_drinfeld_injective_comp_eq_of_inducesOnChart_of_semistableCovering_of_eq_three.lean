-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_exists_linearMap_rationalTateModule_drinfeld_injective_comp_eq_of_inducesOnChart_of_semistableCovering_of_eq_three
-- name    : ModularCurve.FullLevel.exists_linearMap_rationalTateModule_drinfeld_injective_comp_eq_of_inducesOnChart_of_semistableCovering_of_eq_three
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:35.562543+00:00
-- url     : https://prove2.me/theorems/c253e887-c0f4-5474-8ba4-6face149b3d9
-- title:
--   Drinfeld identification on supersingular charts, case q=3
-- statement:
--   Fix a prime $q$ with $q=3$, an integer $M'\neq 0$ with $q\nmid M'$, and a prime $\lambda\neq q$. Assume [`ModularCurve.FullLevel.LevelAutInputs q M'`](def/ModularCurve_FullLevelJacobian.html#L220) (for every index $\zeta$ in the set of primitive $q$-th roots of unity of $\overline{\mathbb{Q}}$ and every $\gamma\in\Gamma_0(M')$ a level automorphism of the field $\mathrm{fieldBar}\,q\,M'=\overline{\mathbb{Q}}\cdot F(\Gamma_H(q^2M'))$ exists) and [`ModularCurve.FullLevel.GL2Laws q M'`](def/ModularCurve_FullLevelJacobian.html#L255) (a monoid map $GL_2(\mathbb{Z}/q)\to\mathrm{End}(\mathrm{Jac}\,q\,M')$ restricting to the $\Gamma_0(M')$-action and to the diagonal action). Let $P$ be a valuation subring of $\overline{\mathbb{Q}}$ with $q$ in its nonunits, $\kappa=\kappa(P)$ its residue field, $W$ a finite set of places of $\mathrm{modularFunctionFieldC}\,\kappa\,M'$ consisting exactly of the supersingular places $\mathrm{ssPlaces}\,q\,M'\,\kappa$, $\pi\in P$ with $\pi^{q^2-1}=q$, and $\iota:\mathbb{F}_{q^2}\to\kappa$ a ring map, the coordinate ring $\mathrm{CoordRing}\,q\,\kappa$ of the Drinfeld curve being a domain. Let $hle$ record $\mathrm{modularFunctionFieldBar}\,M'\le\mathrm{fieldBar}\,q\,M'$ and let $R_0$ be a constant reduction of $\mathrm{modularFunctionFieldBar}\,M'$ to $\mathrm{modularFunctionFieldC}\,\kappa\,M'$ over $P$ whose residue map agrees, on Laurent series with coefficients in $P$, with coefficientwise reduction. Then for every semistable covering $\mathcal{C}$ of $\mathrm{fieldBar}\,q\,M'$ over $P$ indexed by $W$ satisfying the equivariance clauses, a Drinfeld clause $\mathcal{C}.\mathrm{DrinfeldClause}\,\pi\,\iota\,\eta\,\zeta\,s$ for each $\zeta$ and each $s\in W$ with some exponent $\eta\in\{1,q\}$ depending on $(\zeta,s)$, the Igusa unipotent clause for each $\zeta$, the level-pinning clauses for $hle$ and $R_0$, the inertia clause for $\pi$, the width clause for $\pi$, and the genus, discrete-fibre, curve and naturality clauses, there is a family of $\mathbb{Q}_\lambda$-linear maps $$\Phi_{\zeta,s}:\ \mathbb{Q}_\lambda\otimes_{\mathbb{Z}_\lambda}T_\lambda\bigl(\mathrm{Pic}^0_\kappa(\mathcal{C}.\mathrm{teleFbar}(\mathcal{C}.\mathrm{eSS}\,s))\bigr)\longrightarrow \mathbb{Q}_\lambda\otimes_{\mathbb{Z}_\lambda}T_\lambda\bigl(\mathrm{Pic}^0_\kappa(\mathrm{drinfeldFunctionField}\,q\,\kappa)\bigr)$$ such that each $\Phi_{\zeta,s}$ is injective, and: for $\gamma\in SL_2(\mathbb{Z})$ lying in $\Gamma_0(M')$ and every $\kappa$-algebra automorphism $\varphi$ of $\mathcal{C}.\mathrm{teleFbar}(\mathcal{C}.\mathrm{eSS}\,s)$ which induces on the chart $\mathcal{C}.\mathrm{teleChart}(\mathcal{C}.\mathrm{eSS}\,s)$ the semilinear automorphism attached to $\mathrm{levelAutBar}\,q\,M'\,\zeta\,\gamma^{-1}$, one has $\Phi_{\zeta,s}\circ V_\lambda(\varphi)=V_\lambda\bigl(\mathrm{hFunctionFieldAction}(\gamma\bmod q,1)\bigr)\circ\Phi_{\zeta,s}$, for any witness that $(\gamma\bmod q,1)$ lies in $\mathrm{hSubgroup}\,q$; and for $\tau$ in the inertia subgroup of $P$ over $\mathbb{Q}$, $\alpha\in\mathbb{F}_{q^2}^\times$ with $\iota(\alpha)=P.\mathrm{tameCharacter}\,\pi\,\tau$, every $\kappa$-algebra automorphism $\varphi$ inducing on that chart the arithmetic Galois semilinear automorphism of $\tau$ on $\mathrm{xHFunctionField}(q^2M')(\mathrm{levelH}\,q\,M')$, and every $e\in(\mathbb{Z}/q)^\times$ with $(\mathrm{diagOneElem}\,q\,e,\alpha)\in\mathrm{hSubgroup}\,q$, one has $\Phi_{\zeta,s}\circ V_\lambda(\varphi)=V_\lambda\bigl(\mathrm{hFunctionFieldAction}(\mathrm{diagOneElem}\,q\,e,\alpha)\bigr)\circ\Phi_{\zeta,s}$. Here $V_\lambda$ denotes the action on the rational Tate module via [`ModularCurve.rationalGaloisRep`](def/ModularCurve_JZeroTateModule.html#L48).
--
--   This is the $q=3$ form of the identification of the supersingular charts of the semistable covering of the full-level modular curve with (a quotient of) the Drinfeld curve, read on rational $\lambda$-adic Tate modules of the degree-zero divisor class groups, together with the compatibility of the level and tame-inertia actions with the action of the subgroup $\mathrm{hSubgroup}\,q$ of $GL_2(\mathbb{Z}/q)\times\mathbb{F}_{q^2}^\times$. It differs from the generic statement in assuming $q=3$ and in taking the Drinfeld clause per supersingular chart with an exponent $\eta\in\{1,q\}$; it supplies the intertwining map used in the computation of the $q$-adic inertia action on the Tate module product at $q=3$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_exists_linearMap_rationalTateModule_drinfeld_injective_comp_eq_of_inducesOnChart_of_semistableCovering_of_eq_three.lean

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

theorem ModularCurve.FullLevel.exists_linearMap_rationalTateModule_drinfeld_injective_comp_eq_of_inducesOnChart_of_semistableCovering_of_eq_three
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
