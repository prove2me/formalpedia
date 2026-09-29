-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_exists_algEquiv_inducesOnChart_arithmeticGalois_and_red_eq_of_semistableCovering_of_igusaDom_of_eq_two
-- name    : ModularCurve.FullLevel.exists_algEquiv_inducesOnChart_arithmeticGalois_and_red_eq_of_semistableCovering_of_igusaDom_of_eq_two
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:33.630704+00:00
-- url     : https://prove2.me/theorems/b0c79bac-61b1-59e5-b4e7-6ca43fdde960
-- title:
--   Inertia on supersingular charts: induced automorphism and equivariance of red, q=2
-- statement:
--   Let $q$ be a prime with $q=2$, let $M'$ be a nonzero natural number not divisible by $q$, and let $\lambda$ be a prime different from $q$. Assume the level-automorphism input predicate `LevelAutInputs q M'` (every $\zeta$ in the index set of primitive $q$-th roots of unity and every $\gamma\in\Gamma_0(M')$ admit a level automorphism of `fieldBar q M'`) and the predicate `GL2Laws q M'` (a monoid map from $\mathrm{GL}_2(\mathbb{Z}/q)$ to endomorphisms of the Jacobian matching the $\mathrm{SL}_2(\mathbb{Z})$- and diagonal actions). Let $P$ be a valuation subring of $\overline{\mathbb{Q}}$ with $q$ a nonunit of $P$, write $\kappa$ for its residue field, let $W$ be a finset of places of `modularFunctionFieldC κ M'` whose members are exactly the supersingular places `ssPlaces q M' κ`, let $\pi\in P$ satisfy $\pi^{q^2-1}=q$, let $\iota:\mathbb{F}_{q^2}\to\kappa$ be a ring homomorphism making $\kappa$ an $\mathbb{F}_{q^2}$-algebra (the Drinfeld coordinate ring over $\kappa$ being a domain), let `hle` be the inclusion `modularFunctionFieldBar M' ≤ fieldBar q M'`, and let $R_0$ be a constant reduction of `modularFunctionFieldBar M'` to `modularFunctionFieldC κ M'` over $P$ whose residue map agrees, on Laurent series with coefficients in $P$, with coefficientwise reduction. Put $S$ for the set of semilinear automorphisms of `fieldBar q M'` of the form `arithmeticGalois (xHFunctionField (q^2*M') (levelH q M')) τ` with $\tau$ in the inertia subgroup of $P$ over $\mathbb{Q}$ and $P.\mathrm{tameCharacter}\,\pi\,\tau=1$, and let $V^{\mathrm{inv}}$ be the intersection over $s\in S$ of the kernels of $\rho_\lambda(s)-1$ on the rational Tate module $\mathbb{Q}_\lambda\otimes_{\mathbb{Z}_\lambda}T_\lambda\bigl(\mathrm{Pic}^0(\overline{\mathbb{Q}},\,\mathtt{fieldBar}\,q\,M')\bigr)$. Let $\mathcal{C}$ be a semistable covering of type `SemistableCovering q M' P W` satisfying: the equivariance clauses; for each $\zeta$ and each $s\in W$ a Drinfeld clause with a hedged exponent $\eta\in\{1,q\}$; the Igusa unipotent clause for each $\zeta$; the level-pinning clauses relative to `hle` and $R_0$; the inertia clause and the width clause at $\pi$; the genus, discrete-fibre, curve and naturality clauses; and the transport hypothesis that for every inertia element $\tau$ and every $\ell\in\mathbb{P}^1(\mathbb{F}_q)$ there is $\ell'$ with $\mathrm{arithmeticGalois}(\tau)$ carrying the domain of the Igusa chart $\mathcal{C}.\mathrm{CIg}\,\ell$ into that of $\mathcal{C}.\mathrm{CIg}\,\ell'$. Finally let $\mathrm{red}$ be a $\mathbb{Q}_\lambda$-linear map from $V^{\mathrm{inv}}$ to the product over the telescope indices $i$ of the rational Tate modules of $\mathrm{Pic}^0(\kappa,\mathcal{C}.\mathrm{teleFbar}\,i)$ such that: it is computed by divisorwise specialisation (whenever $v\in V^{\mathrm{inv}}$ equals $1\otimes x$, a level-$k$ component of $x$ is the class of a degree-zero divisor $D=\sum_i D_i$ with each $D_i$ supported in the domain of $\mathcal{C}.\mathrm{teleChart}\,i$ and of degree zero, then for each $i$ there is $y$ with $\mathrm{red}\,v\,i=1\otimes y$ whose level-$k$ component is the class of any degree-zero divisor equal to the push-forward of $D_i$ along the chart's place map); $\mathrm{red}\,v=0$ holds exactly when $v$ lies in the $\mathbb{Q}_\lambda$-span of the elements $\rho_\lambda(s)w-w$ with $s\in S$; every $1\otimes x$ in $V^{\mathrm{inv}}$ and every level $k$ admit such a chart-supported degree-zero decomposition; and all places in the chart domains are rational. Then for every $\tau$ in the inertia subgroup of $P$ over $\mathbb{Q}$ and every $s\in W$ there is a $\kappa$-algebra automorphism $\varphi$ of $\mathcal{C}.\mathrm{teleFbar}(\mathcal{C}.\mathrm{eSS}\,s)$ such that $\mathrm{arithmeticGalois}(\tau)$ induces $\varphi$ on the chart $\mathcal{C}.\mathrm{teleChart}(\mathcal{C}.\mathrm{eSS}\,s)$ (membership in the chart's valuation ring is preserved in both directions and the chart residue of $\tau\cdot f$ is $\varphi$ of the residue of $f$), and for every $w\in V^{\mathrm{inv}}$ with $\rho_\lambda(\mathrm{arithmeticGalois}(\tau))w$ again in $V^{\mathrm{inv}}$ one has $\mathrm{red}(\rho_\lambda(\mathrm{arithmeticGalois}(\tau))w)(\mathcal{C}.\mathrm{eSS}\,s)=\rho_\lambda(\varphi)\bigl(\mathrm{red}\,w\,(\mathcal{C}.\mathrm{eSS}\,s)\bigr)$.
--
--   This is the $q=2$ instance of the statement that inertia at a place above $q$ acts on the supersingular components of the semistable covering of the full-level modular curve through genuine $\kappa$-automorphisms of the component function fields, and that the $\lambda$-adic specialisation map $\mathrm{red}$ is equivariant for this action on each supersingular component. It feeds the construction of the inertia-equivariant specialisation of the Tate module used in the analysis of the $\lambda$-adic representation attached to the Jacobian at level $q^2M'$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_exists_algEquiv_inducesOnChart_arithmeticGalois_and_red_eq_of_semistableCovering_of_igusaDom_of_eq_two.lean

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

set_option maxHeartbeats 400000 in

theorem ModularCurve.FullLevel.exists_algEquiv_inducesOnChart_arithmeticGalois_and_red_eq_of_semistableCovering_of_igusaDom_of_eq_two
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

      (∀ τ ∈ P.inertiaSubgroupIn ℚ, ∀ ℓ : CuspidalType.ProjLine q, ∃ ℓ' : CuspidalType.ProjLine q,
        ∀ Q : AlgebraicCurve.Place (AlgebraicClosure ℚ) ↥(ModularCurve.FullLevel.fieldBar q M'), Q ∈ (𝒞.CIg ℓ).dom →
          ModularCurve.arithmeticGalois (ModularCurve.xHFunctionField (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M')) τ • Q ∈
            (𝒞.CIg ℓ').dom) →
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
            ∀ τ ∈ P.inertiaSubgroupIn ℚ, ∀ (s : ↥W),
        ∃ φ : 𝒞.teleFbar (𝒞.eSS s) ≃ₐ[IsLocalRing.ResidueField P] 𝒞.teleFbar (𝒞.eSS s),
          ModularCurve.FullLevel.SemistableCovering.InducesOnChart (𝒞.teleChart (𝒞.eSS s))
              (ModularCurve.arithmeticGalois
                (ModularCurve.xHFunctionField (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M')) τ) φ.toRingEquiv ∧
          ∀ (w : ↥Vinv) (hw : ModularCurve.rationalGaloisRep lam (Pic0 (AlgebraicClosure ℚ) ↥(ModularCurve.FullLevel.fieldBar q M')) (SemilinearAut (AlgebraicClosure ℚ) ↥(ModularCurve.FullLevel.fieldBar q M'))
          (ModularCurve.arithmeticGalois (ModularCurve.xHFunctionField (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M')) τ) (w : ModularCurve.RationalTateModule lam (Pic0 (AlgebraicClosure ℚ) ↥(ModularCurve.FullLevel.fieldBar q M'))) ∈ Vinv),
            red ⟨_, hw⟩ (𝒞.eSS s) = ModularCurve.rationalGaloisRep lam (Pic0 (IsLocalRing.ResidueField P) (𝒞.teleFbar (𝒞.eSS s)))
                (𝒞.teleFbar (𝒞.eSS s) ≃ₐ[IsLocalRing.ResidueField P] 𝒞.teleFbar (𝒞.eSS s)) φ (red w (𝒞.eSS s)) := by sorry
