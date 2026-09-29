-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_exists_algEquiv_inducesOnChart_levelAutBar_and_red_eq_of_semistableCovering_of_eq_three
-- name    : ModularCurve.FullLevel.exists_algEquiv_inducesOnChart_levelAutBar_and_red_eq_of_semistableCovering_of_eq_three
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:33.630704+00:00
-- url     : https://prove2.me/theorems/4b8c8530-7093-5f55-9634-ca381e924538
-- title:
--   Level automorphisms on supersingular charts commute with λ-adic reduction, q=3
-- statement:
--   Fix a prime $q$ with $q = 3$, a level $M'\neq 0$ with $q \nmid M'$, and a prime $\lambda \neq q$; assume the predicates `LevelAutInputs q M'` (for every root-of-unity label $\zeta$ and every $\gamma \in \Gamma_0(M')$ an automorphism of $\overline{\mathbb{Q}}\cdot F(\Gamma_H(q^2M'))$ satisfying `IsLevelAutBar` exists) and `GL2Laws q M'` (the $\Gamma_0(M')$- and diamond-actions on the Jacobian come from a monoid map from $\mathrm{GL}_2(\mathbb{Z}/q)$). Let $P$ be a valuation subring of $\overline{\mathbb{Q}}$ with $q$ in its nonunits, $W$ a finite set of places of $\mathrm{modularFunctionFieldC}$ over the residue field $\kappa = \mathrm{ResidueField}\,P$ consisting exactly of the supersingular places, $\pi \in P$ with $\pi^{q^2-1} = q$, and $\iota : \mathbb{F}_{q^2} \to \kappa$, with the Drinfeld coordinate ring over $\kappa$ a domain; let $R_0$ be a constant reduction of $\overline{\mathbb{Q}}\cdot F(\Gamma(M'))$ to $\mathrm{modularFunctionFieldC}$, compatible with coefficientwise reduction of Laurent series, and $hle$ the inclusion of function fields. Put $S$ for the set of semilinear automorphisms arising as $\mathrm{arithmeticGalois}(\tau)$ for $\tau$ in the inertia subgroup at $P$ with $\mathrm{tameCharacter}\,\pi\,\tau = 1$, and $V^{\mathrm{inv}}$ for the intersection over $s \in S$ of the kernels of $\rho_\lambda(s) - 1$ on the rational Tate module of $\mathrm{Pic}^0$ of the full-level field. Then for every semistable covering $\mathcal{C}$ of that field along $P$ with node set indexed by $W$ satisfying the equivalence clauses, the Drinfeld clause with a per-chart exponent $\eta \in \{1, q\}$ for each $\zeta$ and each $s \in W$, the Igusa unipotent clause for each $\zeta$, the level-pinning clauses for $hle$ and $R_0$, the inertia, width, genus, disc-fibre, curve and naturality clauses, and for every $\mathbb{Q}_\lambda$-linear map $red$ from $V^{\mathrm{inv}}$ to the product over the telescope indices $i$ of the rational Tate modules of $\mathrm{Pic}^0$ of the reduced fields $\mathcal{C}.\mathrm{teleFbar}\,i$ which (i) is computed chartwise on integral representatives: whenever $v \in V^{\mathrm{inv}}$ is $1 \otimes x$, $k \in \mathbb{N}$, and a degree-zero divisor $D$ representing the $k$-th component of $x$ decomposes as $\sum_i D_i$ with each $D_i$ supported in the domain of the $i$-th chart and of degree zero, then $red\,v\,i$ is $1 \otimes y$ for some $y$ whose $k$-th component is the class of the pushforward of $D_i$ along the chart's place map, (ii) has kernel exactly the span of the classes $\rho_\lambda(s)w - w$ for $s \in S$, and (iii) admits such chartwise divisor decompositions for all $v$ and $k$, and assuming all places of the chart domains are rational: for every $\gamma \in \Gamma_0(M')$ in $\mathrm{SL}_2(\mathbb{Z})$, every label $\zeta$ and every $s \in W$, there is a $\kappa$-algebra automorphism $\varphi$ of $\mathcal{C}.\mathrm{teleFbar}(\mathcal{C}.\mathrm{eSS}\,s)$ induced on the chart at $\mathcal{C}.\mathrm{eSS}\,s$ by the semilinear automorphism attached to $\mathrm{levelAutBar}\,q\,M'\,\zeta\,\gamma^{-1}$ (that is, the chart's integers are preserved in both directions and reduction intertwines the two actions), such that for every $w \in V^{\mathrm{inv}}$ whose image under $\rho_\lambda$ of that semilinear automorphism again lies in $V^{\mathrm{inv}}$, one has $red$ of that image at $\mathcal{C}.\mathrm{eSS}\,s$ equal to $\rho_\lambda(\varphi)$ applied to $red\,w$ at $\mathcal{C}.\mathrm{eSS}\,s$.
--
--   This is the naturality of the $\lambda$-adic specialisation map with respect to the level automorphisms, read off on the supersingular (Drinfeld) charts of the semistable covering of the full-level modular curve at $q$, in the case $q = 3$, where the Drinfeld census is supplied point by point with a hedged inertia exponent rather than in uniform form. It feeds the construction of the chartwise Tate-module decomposition used in the local analysis at $q$ of the mod-$q$ representation.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_exists_algEquiv_inducesOnChart_levelAutBar_and_red_eq_of_semistableCovering_of_eq_three.lean

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

open IsLocalRing
open AlgebraicCurve
open scoped TensorProduct

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

theorem ModularCurve.FullLevel.exists_algEquiv_inducesOnChart_levelAutBar_and_red_eq_of_semistableCovering_of_eq_three
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
    let S : Set (SemilinearAut (AlgebraicClosure ℚ) ↥(ModularCurve.FullLevel.fieldBar q M')) :=
      {s | ∃ τ ∈ P.inertiaSubgroupIn ℚ, P.tameCharacter π τ = 1 ∧
        s = ModularCurve.arithmeticGalois (ModularCurve.xHFunctionField (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M')) τ}
    let Vinv : Submodule ℚ_[lam] (ModularCurve.RationalTateModule lam (Pic0 (AlgebraicClosure ℚ) ↥(ModularCurve.FullLevel.fieldBar q M'))) := ⨅ s ∈ S, LinearMap.ker (ModularCurve.rationalGaloisRep lam (Pic0 (AlgebraicClosure ℚ) ↥(ModularCurve.FullLevel.fieldBar q M')) (SemilinearAut (AlgebraicClosure ℚ) ↥(ModularCurve.FullLevel.fieldBar q M')) s - 1)
    ∀ 𝒞 : ModularCurve.FullLevel.SemistableCovering q M' P W,
      𝒞.EquivClauses →
      (∀ (ζ : ModularCurve.FullLevel.Idx q) (s : ↥W), ∃ η : ℕ, (η = 1 ∨ η = q) ∧ 𝒞.DrinfeldClause π ι η ζ s) →
      (∀ ζ : ModularCurve.FullLevel.Idx q, 𝒞.IgusaUnipotentClause ζ) → 𝒞.LevelPinClauses hle R₀ → 𝒞.InertiaClause π →
      𝒞.WidthClause ⟨π, hπP⟩ → 𝒞.GenusClause → 𝒞.DiscFibreClause → 𝒞.CurveClause → 𝒞.NaturalityClauses →
      ∀ (red : ↥Vinv →ₗ[ℚ_[lam]]
      ∀ i, ModularCurve.RationalTateModule lam (Pic0 (IsLocalRing.ResidueField P) (𝒞.teleFbar i))),
      (∀ (v : ↥Vinv)
      (x : TateModule lam (Pic0 (AlgebraicClosure ℚ) ↥(ModularCurve.FullLevel.fieldBar q M'))), (v : ModularCurve.RationalTateModule lam (Pic0 (AlgebraicClosure ℚ) ↥(ModularCurve.FullLevel.fieldBar q M'))) = (1 : ℚ_[lam]) ⊗ₜ[ℤ_[lam]] x →
      ∀ (k : ℕ) (D : Divisor (AlgebraicClosure ℚ) ↥(ModularCurve.FullLevel.fieldBar q M')) (hD : D ∈ Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(ModularCurve.FullLevel.fieldBar q M'))),
      Pic0.mk ⟨D, hD⟩ = TateModule.proj lam (Pic0 (AlgebraicClosure ℚ) ↥(ModularCurve.FullLevel.fieldBar q M')) k x →
      ∀ Di : Fin 𝒞.teleN → Divisor (AlgebraicClosure ℚ) ↥(ModularCurve.FullLevel.fieldBar q M'), D = ∑ i, Di i → (∀ i, ∀ P ∈ (Di i).support, P ∈ (𝒞.teleChart i).dom) →
        (∀ i, Divisor.degree (Di i) = 0) →
        ∀ i, ∃ y : TateModule lam (Pic0 (IsLocalRing.ResidueField P) (𝒞.teleFbar i)),
          red v i = (1 : ℚ_[lam]) ⊗ₜ[ℤ_[lam]] y ∧
          ∀ E : Divisor.degZero (K := IsLocalRing.ResidueField P) (F := 𝒞.teleFbar i),
            (E : Divisor (IsLocalRing.ResidueField P) (𝒞.teleFbar i)) =
                Finsupp.mapDomain (𝒞.teleChart i).placeMap (Di i) →
              TateModule.proj lam (Pic0 (IsLocalRing.ResidueField P) (𝒞.teleFbar i)) k y = Pic0.mk E) →
      (∀ v : ↥Vinv,
      (red v = 0 ↔ (v : ModularCurve.RationalTateModule lam (Pic0 (AlgebraicClosure ℚ) ↥(ModularCurve.FullLevel.fieldBar q M'))) ∈ Submodule.span ℚ_[lam] {u | ∃ s ∈ S, ∃ w,
        u = ModularCurve.rationalGaloisRep lam (Pic0 (AlgebraicClosure ℚ) ↥(ModularCurve.FullLevel.fieldBar q M')) (SemilinearAut (AlgebraicClosure ℚ) ↥(ModularCurve.FullLevel.fieldBar q M')) s w - w})) →
      (∀ (v : ↥Vinv)
      (x : TateModule lam (Pic0 (AlgebraicClosure ℚ) ↥(ModularCurve.FullLevel.fieldBar q M'))), (v : ModularCurve.RationalTateModule lam (Pic0 (AlgebraicClosure ℚ) ↥(ModularCurve.FullLevel.fieldBar q M'))) = (1 : ℚ_[lam]) ⊗ₜ[ℤ_[lam]] x →
      ∀ k : ℕ, ∃ (D : Divisor (AlgebraicClosure ℚ) ↥(ModularCurve.FullLevel.fieldBar q M')) (hD : D ∈ Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(ModularCurve.FullLevel.fieldBar q M'))) (Di : Fin 𝒞.teleN → Divisor (AlgebraicClosure ℚ) ↥(ModularCurve.FullLevel.fieldBar q M')),
        Pic0.mk ⟨D, hD⟩ = TateModule.proj lam (Pic0 (AlgebraicClosure ℚ) ↥(ModularCurve.FullLevel.fieldBar q M')) k x ∧
        D = ∑ i, Di i ∧ (∀ i, ∀ P ∈ (Di i).support, P ∈ (𝒞.teleChart i).dom) ∧ ∀ i, Divisor.degree (Di i) = 0) →
      (∀ i, ∀ Q ∈ (𝒞.teleChart i).dom, Q.IsRational) →
            ∀ (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ), γ ∈ CongruenceSubgroup.Gamma0 M' →
      ∀ (ζ : ModularCurve.FullLevel.Idx q) (s : ↥W),
        ∃ φ : 𝒞.teleFbar (𝒞.eSS s) ≃ₐ[IsLocalRing.ResidueField P] 𝒞.teleFbar (𝒞.eSS s),
          ModularCurve.FullLevel.SemistableCovering.InducesOnChart (𝒞.teleChart (𝒞.eSS s))
              (SemilinearAut.ofAlgAut (ModularCurve.FullLevel.levelAutBar q M' ζ γ⁻¹)) φ.toRingEquiv ∧
          ∀ (w : ↥Vinv) (hw : ModularCurve.rationalGaloisRep lam (Pic0 (AlgebraicClosure ℚ) ↥(ModularCurve.FullLevel.fieldBar q M')) (SemilinearAut (AlgebraicClosure ℚ) ↥(ModularCurve.FullLevel.fieldBar q M'))
          (SemilinearAut.ofAlgAut (ModularCurve.FullLevel.levelAutBar q M' ζ γ⁻¹)) (w : ModularCurve.RationalTateModule lam (Pic0 (AlgebraicClosure ℚ) ↥(ModularCurve.FullLevel.fieldBar q M'))) ∈ Vinv),
            red ⟨_, hw⟩ (𝒞.eSS s) = ModularCurve.rationalGaloisRep lam (Pic0 (IsLocalRing.ResidueField P) (𝒞.teleFbar (𝒞.eSS s)))
                (𝒞.teleFbar (𝒞.eSS s) ≃ₐ[IsLocalRing.ResidueField P] 𝒞.teleFbar (𝒞.eSS s)) φ (red w (𝒞.eSS s)) := by sorry
