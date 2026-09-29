-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_exists_algEquiv_inducesOnChart_arithmeticGalois_and_red_eq_of_semistableCovering_of_igusaDom
-- name    : ModularCurve.FullLevel.exists_algEquiv_inducesOnChart_arithmeticGalois_and_red_eq_of_semistableCovering_of_igusaDom
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:33.630704+00:00
-- url     : https://prove2.me/theorems/73b59b24-448c-55d1-8a69-65a346a3808b
-- title:
--   Inertia on supersingular charts: induced automorphism and naturality of reduction
-- statement:
--   Fix a prime $q \ge 5$, a natural number $M' \neq 0$ with $q \nmid M'$, and a prime $\lambda \neq q$, together with the hypotheses `LevelAutInputs q M'` (each index $\zeta$ and each $\gamma \in \Gamma_0(M')$ admit a level automorphism of `fieldBar q M'` satisfying `IsLevelAutBar`) and `GL2Laws q M'` (existence of a $\mathrm{GL}_2(\mathbb{Z}/q)$-action on the Jacobian restricting to the $\Gamma_0(M')$-action and to the diamond operators). Let $P$ be a valuation subring of $\overline{\mathbb{Q}}$ with $q$ a non-unit of $P$, let $W$ be a finset of places of `modularFunctionFieldC (ResidueField P) M'` whose members are exactly the supersingular places `ssPlaces q M'`, let $\pi \in P$ satisfy $\pi^{q^2-1} = q$, let $\iota : \mathbb{F}_{q^2} \to \mathrm{ResidueField}\,P$ be a ring homomorphism (making the residue field an $\mathbb{F}_{q^2}$-algebra), and assume [`DrinfeldCurve.CoordRing q (ResidueField P)`](def/DrinfeldCurve_CoordRing.html#L21) is a domain. Assume `modularFunctionFieldBar M' ≤ fieldBar q M'` and let $R_0$ be a constant reduction of the level-$M'$ function field over $P$ with values in `modularFunctionFieldC (ResidueField P) M'`, compatible with coefficientwise reduction in the sense that for every Laurent series $y$ over $P$ whose coefficientwise image lies in `modularFunctionFieldBar M'`, that image lies in $R_0.\mathrm{integers}$ and its $R_0$-residue, read as a Laurent series over the residue field, is the coefficientwise residue of $y$. Put $S$ for the set of semilinear automorphisms `arithmeticGalois (xHFunctionField (q^2*M') (levelH q M')) τ` with $\tau$ in the inertia subgroup of $P$ over $\mathbb{Q}$ and tame character $P.\mathrm{tameCharacter}\,\pi\,\tau = 1$, and let $V_{\mathrm{inv}}$ be the intersection over $s \in S$ of the kernels of $\rho(s) - 1$ on the rational $\lambda$-adic Tate module of $\mathrm{Pic}^0$ of `fieldBar q M'`. The assertion is: for every semistable covering $\mathcal{C}$ of `fieldBar q M'` over $P$ indexed by $W$ satisfying the clauses `EquivClauses`, `W2Clauses π ι q`, `LevelPinClauses hle R₀`, `InertiaClause π`, `WidthClause ⟨π, hπP⟩`, `GenusClause`, `DiscFibreClause`, `CurveClause` and `NaturalityClauses`; assuming further that each inertia element carries the domain of every Igusa chart $\mathcal{C}.\mathrm{CIg}\,\ell$ into the domain of some $\mathcal{C}.\mathrm{CIg}\,\ell'$; and given a $\mathbb{Q}_\lambda$-linear map $\mathrm{red}$ from $V_{\mathrm{inv}}$ to the product over $i < \mathcal{C}.\mathrm{teleN}$ of the rational $\lambda$-adic Tate modules of $\mathrm{Pic}^0$ of the telescope fields $\mathcal{C}.\mathrm{teleFbar}\,i$ such that (1) whenever $v \in V_{\mathrm{inv}}$ is $1 \otimes x$, the class of a degree-zero divisor $D$ is the $k$-th projection of $x$, and $D = \sum_i D_i$ with each $D_i$ of degree zero and supported in the domain of $\mathcal{C}.\mathrm{teleChart}\,i$, then each $\mathrm{red}\,v\,i$ is $1 \otimes y$ with $k$-th projection the class of the pushforward of $D_i$ along the chart's place map, (2) $\mathrm{red}\,v = 0$ exactly when $v$ lies in the $\mathbb{Q}_\lambda$-span of the elements $\rho(s)w - w$ for $s \in S$, (3) every $v = 1 \otimes x$ in $V_{\mathrm{inv}}$ and every $k$ admit such a chart-supported degree-zero decomposition of a divisor representing the $k$-th projection of $x$, and (4) all places in the chart domains are rational: then for every $\tau$ in the inertia subgroup of $P$ over $\mathbb{Q}$ and every $s \in W$ there is a $\mathrm{ResidueField}\,P$-algebra automorphism $\varphi$ of $\mathcal{C}.\mathrm{teleFbar}(\mathcal{C}.\mathrm{eSS}\,s)$ which `arithmeticGalois … τ` induces on the chart $\mathcal{C}.\mathrm{teleChart}(\mathcal{C}.\mathrm{eSS}\,s)$ (the chart's integers are preserved and its residue map intertwines the two actions), and such that for every $w \in V_{\mathrm{inv}}$ with $\rho(\mathrm{arithmeticGalois}\,\tau)(w)$ again in $V_{\mathrm{inv}}$ one has $\mathrm{red}(\rho(\mathrm{arithmeticGalois}\,\tau)w)$ at the index $\mathcal{C}.\mathrm{eSS}\,s$ equal to $\rho(\varphi)$ applied to $\mathrm{red}\,w$ at that index.
--
--   This is the equivariance of the specialisation map on the $\lambda$-adic Tate module of the Jacobian along the supersingular components of the semistable covering of the full-level modular curve: inertia at $q$ acts on each supersingular chart through an automorphism of its reduced function field, and reduction of divisor classes commutes with that action. It feeds the construction of the reduction map on the inertia-invariants used in the analysis of the $\lambda$-adic representation attached to $J_H$ at $q$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_exists_algEquiv_inducesOnChart_arithmeticGalois_and_red_eq_of_semistableCovering_of_igusaDom.lean

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

theorem ModularCurve.FullLevel.exists_algEquiv_inducesOnChart_arithmeticGalois_and_red_eq_of_semistableCovering_of_igusaDom
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
