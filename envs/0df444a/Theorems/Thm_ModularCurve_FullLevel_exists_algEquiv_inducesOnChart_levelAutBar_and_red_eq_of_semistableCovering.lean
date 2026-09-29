-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_exists_algEquiv_inducesOnChart_levelAutBar_and_red_eq_of_semistableCovering
-- name    : ModularCurve.FullLevel.exists_algEquiv_inducesOnChart_levelAutBar_and_red_eq_of_semistableCovering
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:33.630704+00:00
-- url     : https://prove2.me/theorems/aae6924a-83b0-5dec-910d-09ca1a5f7cbe
-- title:
--   Naturality of λ-adic reduction under level automorphisms
-- statement:
--   Fix primes $q\ge 5$ and $\lambda\ne q$, and $M'\ne 0$ with $q\nmid M'$; assume `LevelAutInputs q M'` and `GL2Laws q M'`. Let $P\subset\overline{\mathbb Q}$ be a valuation subring with $q$ a non-unit of $P$, let $\kappa=$ `ResidueField P`, let $W$ be a finset of places of `modularFunctionFieldC κ M'` whose members are exactly the supersingular places `ssPlaces q M' κ`, let $\pi\in P$ satisfy $\pi^{q^2-1}=q$, and let $\iota:\mathbb F_{q^2}\to\kappa$ be a ring map (making $\kappa$ an $\mathbb F_{q^2}$-algebra), with [`DrinfeldCurve.CoordRing q κ`](def/DrinfeldCurve_CoordRing.html#L21) a domain. Assume `modularFunctionFieldBar M' ≤ fieldBar q M'` and let $R_0$ be a constant reduction of the former with values in `modularFunctionFieldC κ M'` whose residue map computes coefficientwise reduction of Laurent series over $P$ (hypothesis `hR₀`). Write $S$ for the set of semilinear automorphisms `arithmeticGalois … τ` with $\tau$ in the inertia subgroup of $P$ over $\mathbb Q$ and `tameCharacter π τ = 1`, and $V^{\mathrm{inv}}$ for the intersection over $s\in S$ of the kernels of $\rho(s)-1$ on the rational $\lambda$-adic Tate module of $\mathrm{Pic}^0$ of `fieldBar q M'`. Let $\mathcal C$ be a `SemistableCovering q M' P W` satisfying its nine clauses (`EquivClauses`, `W2Clauses π ι q`, `LevelPinClauses`, `InertiaClause π`, `WidthClause`, `GenusClause`, `DiscFibreClause`, `CurveClause`, `NaturalityClauses`), and let $\mathrm{red}$ be a $\mathbb Q_\lambda$-linear map from $V^{\mathrm{inv}}$ to the product over $i<\mathcal C.\mathrm{teleN}$ of the rational $\lambda$-adic Tate modules of $\mathrm{Pic}^0(\mathcal C.\mathrm{teleFbar}\,i)$ such that: (i) whenever $v\in V^{\mathrm{inv}}$ is $1\otimes x$, $D$ is a degree-zero divisor representing the $k$-th component of $x$, and $D=\sum_i D_i$ with each $D_i$ of degree zero and supported in the domain of $\mathcal C.\mathrm{teleChart}\,i$, then for each $i$ there is an integral Tate vector $y$ with $\mathrm{red}\,v\,i=1\otimes y$ whose $k$-th component is the class of any degree-zero divisor equal to the pushforward of $D_i$ along the chart's `placeMap`; (ii) $\mathrm{red}\,v=0$ exactly when $v$ lies in the $\mathbb Q_\lambda$-span of the $\rho(s)w-w$ for $s\in S$; (iii) such decompositions $D=\sum_iD_i$ exist for every $v$ and every $k$; (iv) all places in the chart domains are rational. Then for every $\gamma\in SL_2(\mathbb Z)$ lying in $\Gamma_0(M')$, every $\zeta$ in `Idx q` and every $s\in W$ there is a $\kappa$-algebra automorphism $\varphi$ of $\mathcal C.\mathrm{teleFbar}(\mathcal C.\mathrm{eSS}\,s)$ such that the semilinear automorphism `ofAlgAut (levelAutBar q M' ζ γ⁻¹)` induces $\varphi$ on the chart $\mathcal C.\mathrm{teleChart}(\mathcal C.\mathrm{eSS}\,s)$ in the sense of `InducesOnChart`, and for every $w\in V^{\mathrm{inv}}$ whose image under $\rho$ of `ofAlgAut (levelAutBar q M' ζ γ⁻¹)` again lies in $V^{\mathrm{inv}}$, the $(\mathcal C.\mathrm{eSS}\,s)$-component of $\mathrm{red}$ of that image equals $\rho(\varphi)$ applied to the $(\mathcal C.\mathrm{eSS}\,s)$-component of $\mathrm{red}\,w$.
--
--   This is the level-automorphism case of the equivariance of specialisation of the Jacobian of the full-level modular curve at a place above $q$: the automorphisms `levelAutBar q M' ζ γ⁻¹` act on the supersingular charts of the semistable covering and the $\lambda$-adic reduction map intertwines their action with that of the induced automorphisms of the reduced function fields. It is used in the assembly of the product decomposition of the reduction map on tame-inertia invariants, where it supplies the required naturality input for the level action.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_exists_algEquiv_inducesOnChart_levelAutBar_and_red_eq_of_semistableCovering.lean

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

theorem ModularCurve.FullLevel.exists_algEquiv_inducesOnChart_levelAutBar_and_red_eq_of_semistableCovering
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
    let S : Set (SemilinearAut (AlgebraicClosure ℚ) ↥(ModularCurve.FullLevel.fieldBar q M')) :=
      {s | ∃ τ ∈ P.inertiaSubgroupIn ℚ, P.tameCharacter π τ = 1 ∧
        s = ModularCurve.arithmeticGalois (ModularCurve.xHFunctionField (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M')) τ}
    let Vinv : Submodule ℚ_[lam] (ModularCurve.RationalTateModule lam (Pic0 (AlgebraicClosure ℚ) ↥(ModularCurve.FullLevel.fieldBar q M'))) := ⨅ s ∈ S, LinearMap.ker (ModularCurve.rationalGaloisRep lam (Pic0 (AlgebraicClosure ℚ) ↥(ModularCurve.FullLevel.fieldBar q M')) (SemilinearAut (AlgebraicClosure ℚ) ↥(ModularCurve.FullLevel.fieldBar q M')) s - 1)
    ∀ 𝒞 : ModularCurve.FullLevel.SemistableCovering q M' P W,
      𝒞.EquivClauses → 𝒞.W2Clauses π ι q → 𝒞.LevelPinClauses hle R₀ → 𝒞.InertiaClause π →
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
