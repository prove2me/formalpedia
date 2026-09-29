-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_telescope_frame_of_semistableCovering_of_eq_three
-- name    : ModularCurve.FullLevel.telescope_frame_of_semistableCovering_of_eq_three
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:39.1924+00:00
-- url     : https://prove2.me/theorems/45193f08-e1cf-5fd6-acec-2e6bd5e635e3
-- title:
--   Telescope frame for the full-level semistable covering, q=3
-- statement:
--   Let $q$ be a prime with $q=3$, let $M'$ be a non-zero natural number not divisible by $q$, and let $\lambda$ be a prime different from $q$; assume the predicates [`ModularCurve.FullLevel.LevelAutInputs`](def/ModularCurve_FullLevelJacobian.html#L220) and [`ModularCurve.FullLevel.GL2Laws`](def/ModularCurve_FullLevelJacobian.html#L255) for $q,M'$ (existence of level automorphisms of $\bar{\mathbb{Q}}\cdot F(\Gamma_H(q^2M'))$ over $\Gamma_0(M')$, and a $\mathrm{GL}_2(\mathbb{Z}/q)$-action on the Jacobian compatible with the $\Gamma_0(M')$- and diagonal actions). Let $P$ be a valuation subring of an algebraic closure of $\mathbb{Q}$ with $q$ a non-unit of $P$, let $W$ be a finset of places of $\mathrm{modularFunctionFieldC}$ over the residue field $\kappa(P)$ whose members are exactly the supersingular places [`ModularCurve.ssPlaces`](def/ModularCurve_SupersingularNodePlaces.html#L113), let $\pi\in P$ satisfy $\pi^{q^2-1}=q$, and let $\iota:\mathbb{F}_{q^2}\to\kappa(P)$ be a ring homomorphism, the Drinfeld coordinate ring over $\kappa(P)$ being a domain. Let $\mathrm{hle}$ be the inclusion of the base-changed modular function field of level $M'$ into $\mathrm{fieldBar}\,q\,M'$ and $R_0$ a constant reduction of the former whose residue map agrees, on Laurent series with coefficients in $P$, with coefficientwise reduction modulo the maximal ideal (hypothesis $\mathrm{hR}_0$). Set $S$ to be the set of semilinear automorphisms of $\mathrm{fieldBar}\,q\,M'$ of the form $\mathrm{arithmeticGalois}(\tau)$ with $\tau$ in the inertia subgroup of $P$ over $\mathbb{Q}$ and tame character $\tau\mapsto\iota$-valued residue of $\tau\pi/\pi$ equal to $1$. Then for every semistable covering $\mathcal{C}$ of $\mathrm{fieldBar}\,q\,M'$ along $P$ with supersingular index set $W$ satisfying its equivariance clauses, a Drinfeld clause for each pair $(\zeta,s)$ of a primitive $q$-th root of unity and a supersingular point with some inertia exponent $\eta\in\{1,q\}$, the Igusa unipotent clause for every $\zeta$, the level-pinning, inertia, width, genus, discrete-fibre, curve and naturality clauses, the following all hold: $\pi$ is a non-zero element of the maximal ideal of $P$; for every non-zero $x$ and every $y$ in the maximal ideal some power $y^n$ has valuation at most that of $x$; every place in the domain of every telescope chart $\mathcal{C}.\mathrm{teleChart}\,i$ is rational; every $s\in S$ has base automorphism preserving membership in $P$, fixing $\pi$, inducing the identity on $\kappa(P)$, and $s$ preserves each telescope chart domain and each telescope annulus domain, fixes the parameters of $\mathcal{C}.\mathrm{teleAn}\,e$ and $\mathcal{C}.\mathrm{teleAn}'\,e$, preserves each chart's integers with unchanged residues, and leaves each chart's place map invariant on its domain; conversely every ring automorphism of the algebraic closure preserving $P$, fixing $\pi$ and acting trivially on $\kappa(P)$ is the base automorphism of some $s\in S$; $\lambda$ is a unit in $\kappa(P)$; some $s\in S$ moves some $\lambda$-th root of $\pi$; every node of every telescope chart occurs as the source end or the target end of some telescope edge, and occurs exactly once among the $2\,\mathcal{C}.\mathrm{teleM}$ ends; the $\lambda$-adic rational Tate module $\mathbb{Q}_\lambda\otimes_{\mathbb{Z}_\lambda}T_\lambda\,\mathrm{Pic}^0$ of $\mathrm{fieldBar}\,q\,M'$ is finite-dimensional over $\mathbb{Q}_\lambda$; and $\mathrm{fieldBar}\,q\,M'$ is a curve over the algebraic closure of $\mathbb{Q}$ and essentially of finite type over it.
--
--   This is the interface statement verifying, for $q=3$, that the explicit semistable covering of the full-level modular curve $X_H(q^2M')$ together with the tame-inertia action satisfies the hypothesis block of the generic theorems on semistable coverings: rank-one and residue properties of the place $P$, rationality of chart points, the group $S$ of covering automorphisms coming from tame inertia with trivial tame character, the combinatorics of nodes and annulus ends, and finiteness of the $\lambda$-adic Tate module. It is used by the two full-level results extracting the Tate-module linear map and the bound on the image of $\mathrm{tateGal}-1$ in the span of the unipotent-fixed part.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_telescope_frame_of_semistableCovering_of_eq_three.lean

import Definitions.Def_ModularCurve_FullLevelSemistableCoveringTelescope
import Definitions.Def_ModularCurve_FullLevelSemistableCoveringGuards
import Definitions.Def_ModularCurve_FullLevelSemistableCoveringNaturality
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_ModularCurve_JZeroTateModule
import Definitions.Def_AlgebraicCurve_IsCurveOver

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve IsLocalRing
open scoped TensorProduct

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

theorem ModularCurve.FullLevel.telescope_frame_of_semistableCovering_of_eq_three
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
    ∀ 𝒞 : ModularCurve.FullLevel.SemistableCovering q M' P W,
      𝒞.EquivClauses →
      (∀ (ζ : ModularCurve.FullLevel.Idx q) (s : ↥W), ∃ η : ℕ, (η = 1 ∨ η = q) ∧ 𝒞.DrinfeldClause π ι η ζ s) →
      (∀ ζ : ModularCurve.FullLevel.Idx q, 𝒞.IgusaUnipotentClause ζ) → 𝒞.LevelPinClauses hle R₀ → 𝒞.InertiaClause π →
      𝒞.WidthClause ⟨π, hπP⟩ → 𝒞.GenusClause → 𝒞.DiscFibreClause → 𝒞.CurveClause → 𝒞.NaturalityClauses →
      ((⟨π, hπP⟩ : P) ∈ IsLocalRing.maximalIdeal P ∧ (⟨π, hπP⟩ : P) ≠ 0) ∧
      (∀ x : AlgebraicClosure ℚ, x ≠ 0 → ∀ y : P, y ∈ IsLocalRing.maximalIdeal P →
        ∃ n : ℕ, P.valuation ((y : AlgebraicClosure ℚ) ^ n) ≤ P.valuation x) ∧
      (∀ i, ∀ Q ∈ (𝒞.teleChart i).dom, Q.IsRational) ∧
      (∀ s ∈ S,
        (∀ a : AlgebraicClosure ℚ, a ∈ P ↔ SemilinearAut.baseAut s a ∈ P) ∧
        SemilinearAut.baseAut s ((⟨π, hπP⟩ : P) : AlgebraicClosure ℚ) = ((⟨π, hπP⟩ : P) : AlgebraicClosure ℚ) ∧
        (∀ (a : P) (h : SemilinearAut.baseAut s (a : AlgebraicClosure ℚ) ∈ P),
          IsLocalRing.residue P ⟨SemilinearAut.baseAut s (a : AlgebraicClosure ℚ), h⟩ = IsLocalRing.residue P a) ∧
        (∀ i, ∀ Q ∈ (𝒞.teleChart i).dom, s • Q ∈ (𝒞.teleChart i).dom) ∧
        (∀ e, ∀ Q ∈ (𝒞.teleAn e).dom, s • Q ∈ (𝒞.teleAn e).dom) ∧
        (∀ e, s • (𝒞.teleAn e).param = (𝒞.teleAn e).param) ∧ (∀ e, s • (𝒞.teleAn' e).param = (𝒞.teleAn' e).param) ∧
        (∀ i, ∀ f : ↥(ModularCurve.FullLevel.fieldBar q M'), ∀ hf : f ∈ (𝒞.teleChart i).integers,
          ∃ hf' : s • f ∈ (𝒞.teleChart i).integers,
          (𝒞.teleChart i).residue ⟨s • f, hf'⟩ = (𝒞.teleChart i).residue ⟨f, hf⟩) ∧
        (∀ i, ∀ Q ∈ (𝒞.teleChart i).dom, (𝒞.teleChart i).placeMap (s • Q) = (𝒞.teleChart i).placeMap Q)) ∧
      (∀ σ : AlgebraicClosure ℚ ≃+* AlgebraicClosure ℚ, (∀ a : AlgebraicClosure ℚ, a ∈ P ↔ σ a ∈ P) →
        σ ((⟨π, hπP⟩ : P) : AlgebraicClosure ℚ) = ((⟨π, hπP⟩ : P) : AlgebraicClosure ℚ) →
        (∀ (a : P) (h : σ (a : AlgebraicClosure ℚ) ∈ P),
          IsLocalRing.residue P ⟨σ (a : AlgebraicClosure ℚ), h⟩ = IsLocalRing.residue P a) →
        ∃ s ∈ S, SemilinearAut.baseAut s = σ) ∧
      IsUnit ((lam : ℕ) : IsLocalRing.ResidueField P) ∧
      (∃ s ∈ S, ∃ r : AlgebraicClosure ℚ, r ^ lam = ((⟨π, hπP⟩ : P) : AlgebraicClosure ℚ) ∧
        SemilinearAut.baseAut s r ≠ r) ∧
      ((∀ i, ∀ x ∈ (𝒞.teleChart i).nodes, ∃ e,
          (⟨𝒞.teleSrc e, 𝒞.teleXs e⟩ : Σ j, Place (IsLocalRing.ResidueField P) (𝒞.teleFbar j)) = ⟨i, x⟩ ∨
          (⟨𝒞.teleTgt e, 𝒞.teleXt e⟩ : Σ j, Place (IsLocalRing.ResidueField P) (𝒞.teleFbar j)) = ⟨i, x⟩) ∧
        (∀ i, ∀ x ∈ (𝒞.teleChart i).nodes, ∀ E E' : Fin 𝒞.teleM ⊕ Fin 𝒞.teleM,
          Sum.elim (fun e => (⟨𝒞.teleSrc e, 𝒞.teleXs e⟩ : Σ j, Place (IsLocalRing.ResidueField P) (𝒞.teleFbar j)))
            (fun e => ⟨𝒞.teleTgt e, 𝒞.teleXt e⟩) E = ⟨i, x⟩ →
          Sum.elim (fun e => (⟨𝒞.teleSrc e, 𝒞.teleXs e⟩ : Σ j, Place (IsLocalRing.ResidueField P) (𝒞.teleFbar j)))
            (fun e => ⟨𝒞.teleTgt e, 𝒞.teleXt e⟩) E' = ⟨i, x⟩ → E = E')) ∧
      FiniteDimensional ℚ_[lam] (ModularCurve.RationalTateModule lam (Pic0 (AlgebraicClosure ℚ) ↥(ModularCurve.FullLevel.fieldBar q M'))) ∧
      IsCurveOver (AlgebraicClosure ℚ) ↥(ModularCurve.FullLevel.fieldBar q M') ∧ Algebra.EssFiniteType (AlgebraicClosure ℚ) ↥(ModularCurve.FullLevel.fieldBar q M') := by sorry
