-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_exists_algEquiv_inducesOnChart_levelAutBar_and_red_eq_of_semistableCovering_of_eq_two
-- name    : ModularCurve.FullLevel.exists_algEquiv_inducesOnChart_levelAutBar_and_red_eq_of_semistableCovering_of_eq_two
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:33.630704+00:00
-- url     : https://prove2.me/theorems/8c9b6083-c569-5b8f-85eb-c8dcfb7e4f71
-- title:
--   Level automorphisms commute with λ-adic reduction on supersingular charts (q=2)
-- statement:
--   Fix primes $q$ and $\lambda$ with $q\ne\lambda$ and $q=2$, and a level $M'\neq 0$ with $q\nmid M'$; assume `LevelAutInputs` (for each primitive $q$-th root of unity $\zeta$ and each $\gamma\in\Gamma_0(M')$ an automorphism of $\overline{\mathbb Q}\cdot F(\Gamma_H(q^2M'))$ satisfying `IsLevelAutBar` exists) and `GL2Laws` (the $\mathrm{GL}_2(\mathbb Z/q)$-action on the Jacobian compatible with $\Gamma_0(M')$-matrices and with diagonal elements). Let $P$ be a valuation subring of $\overline{\mathbb Q}$ with $q$ a nonunit of $P$, let $W$ be the finite set of supersingular places of $\mathrm{modularFunctionFieldC}(\kappa,M')$, $\kappa$ the residue field of $P$, let $\pi\in P$ satisfy $\pi^{q^2-1}=q$, and let $\iota:\mathbb F_{q^2}\to\kappa$ be a ring homomorphism, the Drinfeld coordinate ring over $\kappa$ being a domain. Let $\mathrm{modularFunctionFieldBar}(M')\le \mathrm{fieldBar}(q,M')$ and let $R_0$ be a constant reduction of the former along $P$ whose residue agrees coefficientwise with reduction of Laurent series ($hR_0$). Put $S$ for the set of semilinear automorphisms $\mathrm{arithmeticGalois}(\tau)$ with $\tau$ in the inertia subgroup at $P$ and tame character $1$, and $V^{\mathrm{inv}}=\bigcap_{s\in S}\ker(\rho_\lambda(s)-1)$ inside the rational $\lambda$-adic Tate module of $\mathrm{Pic}^0$ of $\mathrm{fieldBar}(q,M')$. Let $\mathcal C$ be a semistable covering over $P$ indexed by $W$ satisfying: the equivariance clauses; for each $\zeta$ and each $s\in W$ a Drinfeld clause with exponent $\eta\in\{1,q\}$; the Igusa unipotent clause for every $\zeta$; the level-pinning clauses relative to $hle$ and $R_0$; the inertia, width (with $\pi$), genus, discrete-fibre, curve and naturality clauses. Let $\mathrm{red}$ be a $\mathbb Q_\lambda$-linear map from $V^{\mathrm{inv}}$ to the product over the telescope indices $i$ of the rational Tate modules of $\mathrm{Pic}^0$ of $\mathcal C.\mathrm{teleFbar}\,i$, assumed to satisfy: the divisorwise reduction law (if $v=1\otimes x$ and the $k$-th projection of $x$ is the class of a degree-zero divisor $D=\sum_i D_i$ with each $D_i$ supported in the $i$-th chart domain and of degree zero, then $\mathrm{red}\,v\,i=1\otimes y$ for some $y$ whose $k$-th projection is the class of any degree-zero divisor equal to the push-forward of $D_i$ along the chart's place map); vanishing of $\mathrm{red}\,v$ exactly when $v$ lies in the $\mathbb Q_\lambda$-span of the elements $\rho_\lambda(s)w-w$, $s\in S$; existence of such decompositions $D=\sum_i D_i$ for every $v$, $x$ and $k$; and rationality of every place in every chart domain. Then for every $\gamma\in\mathrm{SL}_2(\mathbb Z)$ lying in $\Gamma_0(M')$, every $\zeta$ and every $s\in W$ there is a $\kappa$-algebra automorphism $\varphi$ of $\mathcal C.\mathrm{teleFbar}(\mathcal C.\mathrm{eSS}\,s)$ such that the semilinear automorphism attached to $\mathrm{levelAutBar}(q,M',\zeta,\gamma^{-1})$ preserves the integers of the chart $\mathcal C.\mathrm{teleChart}(\mathcal C.\mathrm{eSS}\,s)$ and induces $\varphi$ on its residue field, and such that for every $w\in V^{\mathrm{inv}}$ whose image under $\rho_\lambda(\mathrm{levelAutBar}(q,M',\zeta,\gamma^{-1}))$ again lies in $V^{\mathrm{inv}}$, the component of $\mathrm{red}$ of that image at the index $\mathcal C.\mathrm{eSS}\,s$ equals $\rho_\lambda(\varphi)$ applied to $\mathrm{red}\,w$ at that index.
--
--   This is the naturality of the $\lambda$-adic specialisation map on the supersingular (Drinfeld) components of the semistable covering of the full-level modular curve at a prime above $q$, in the form used when $q=2$: the level automorphisms attached to $\Gamma_0(M')$-matrices act on the reduced fibre fields and commute with reduction of tame-inertia invariant Tate classes. It feeds the construction of the comparison map between the tame-inertia invariants and the product of the Tate modules of the components, via [`ModularCurve.FullLevel.exists_linearMap_tateProd_comp_baseChange_eq_and_eq_zero_of_semistableCovering_of_semistableModel_of_reduction_of_inertiaIgusa_of_eq_two`](thm.html#ModularCurve.FullLevel.exists_linearMap_tateProd_comp_baseChange_eq_and_eq_zero_of_semistableCovering_of_semistableModel_of_reduction_of_inertiaIgusa_of_eq_two); the commutation of arithmetic Galois with the level automorphisms is supplied by [`ModularCurve.FullLevel.arithmeticGalois_mul_ofAlgAut_levelAutBar_of_tameCharacter_eq_one`](thm.html#ModularCurve.FullLevel.arithmeticGalois_mul_ofAlgAut_levelAutBar_of_tameCharacter_eq_one), and the chartwise transport of classes by [`AlgebraicCurve.red_rationalGaloisRep_apply_eq_rationalGaloisRep_red_of_inducesOnChart_of_placeMap_smul_of_isRational_of_mem_invariants`](thm.html#AlgebraicCurve.red_rationalGaloisRep_apply_eq_rationalGaloisRep_red_of_inducesOnChart_of_placeMap_smul_of_isRational_of_mem_invariants).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_exists_algEquiv_inducesOnChart_levelAutBar_and_red_eq_of_semistableCovering_of_eq_two.lean

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

theorem ModularCurve.FullLevel.exists_algEquiv_inducesOnChart_levelAutBar_and_red_eq_of_semistableCovering_of_eq_two
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
