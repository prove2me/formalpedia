-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_telescope_frame_of_semistableCovering
-- name    : ModularCurve.FullLevel.telescope_frame_of_semistableCovering
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:39.1924+00:00
-- url     : https://prove2.me/theorems/f935daa6-ebee-5ff8-92e7-1b7fd9bebf40
-- title:
--   Tame inertia frame for the full-level telescope
-- statement:
--   Fix a prime $q\ge 5$, an integer $M'\neq 0$ not divisible by $q$, and a prime $\lambda\neq q$. Assume [`ModularCurve.FullLevel.LevelAutInputs q M'`](def/ModularCurve_FullLevelJacobian.html#L220) (for every $\zeta$ in `Idx q` and every $\gamma\in\Gamma_0(M')$ there is an automorphism of $\overline{\mathbb{Q}}$-algebras of `fieldBar q M'` satisfying `IsLevelAutBar`) and [`ModularCurve.FullLevel.GL2Laws q M'`](def/ModularCurve_FullLevelJacobian.html#L255) (a monoid homomorphism from $\mathrm{GL}_2(\mathbb{Z}/q)$ to the additive endomorphisms of the Jacobian matching `slJac` on $\Gamma_0(M')$ and `diagJac` on the diagonal elements). Let $P$ be a valuation subring of $\overline{\mathbb{Q}}$ with $q$ a nonunit of $P$, let $W$ be a finite set of places of `modularFunctionFieldC (ResidueField P) M'` whose members are exactly the supersingular places `ssPlaces q M'`, let $\pi\in P$ satisfy $\pi^{q^2-1}=q$, let $\iota:\mathbb{F}_{q^2}\to\kappa(P)$ be a ring homomorphism (through which $\kappa(P)$ becomes an $\mathbb{F}_{q^2}$-algebra), with [`DrinfeldCurve.CoordRing q (ResidueField P)`](def/DrinfeldCurve_CoordRing.html#L21) a domain; let `modularFunctionFieldBar M'` $\le$ `fieldBar q M'` via $hle$, and let $R_0$ be a constant reduction along $P$ of `modularFunctionFieldBar M'` to `modularFunctionFieldC (ResidueField P) M'` which is compatible with coefficientwise reduction: every Laurent series $y$ over $P$ whose coefficientwise image lies in `modularFunctionFieldBar M'` gives an element of $R_0$.`integers` whose $R_0$-residue is, as a Laurent series over $\kappa(P)$, the coefficientwise reduction of $y$. Put $S$ for the set of semilinear automorphisms of `fieldBar q M'` over $\overline{\mathbb{Q}}$ of the form `arithmeticGalois` of $\tau$, where $\tau$ lies in the inertia subgroup of $P$ over $\mathbb{Q}$ and $P$.`tameCharacter` $\pi\,\tau=1$. Then for every $\mathcal{C}$ : `SemistableCovering q M' P W` satisfying its nine clauses (`EquivClauses`, `W2Clauses π ι q`, `LevelPinClauses hle R₀`, `InertiaClause π`, `WidthClause`, `GenusClause`, `DiscFibreClause`, `CurveClause`, `NaturalityClauses`) the following hold simultaneously: $\pi$ is a nonzero element of the maximal ideal of $P$; for every $x\neq 0$ and every $y$ in the maximal ideal of $P$ some power $y^n$ has valuation at most that of $x$; every place in the domain of every telescope chart `teleChart i` is rational; every $s\in S$ has base automorphism preserving $P$, fixing $\pi$ and inducing the identity on $\kappa(P)$, preserves the domain of each `teleChart i` and of each `teleAn e`, fixes the parameters of all `teleAn e` and `teleAn' e`, carries `teleChart i`.`integers` into itself with unchanged residues, and leaves `placeMap` invariant on chart domains; conversely every ring automorphism of $\overline{\mathbb{Q}}$ preserving $P$, fixing $\pi$ and acting trivially on $\kappa(P)$ is the base automorphism of some $s\in S$; $\lambda$ is a unit in $\kappa(P)$; some $s\in S$ moves some $\lambda$-th root of $\pi$; each node of each telescope chart is an endpoint $(\mathtt{teleSrc},\mathtt{teleXs})$ or $(\mathtt{teleTgt},\mathtt{teleXt})$ of some edge, and it is so for exactly one element of `Fin 𝒞.teleM ⊕ Fin 𝒞.teleM`; the $\lambda$-adic rational Tate module of `Pic0` of `fieldBar q M'` is finite-dimensional over $\mathbb{Q}_\lambda$; and `fieldBar q M'` is a curve over $\overline{\mathbb{Q}}$ in the sense of `IsCurveOver` and is essentially of finite type over it.
--
--   This conjunction is precisely the hypothesis block of the general semistable-covering theorems (reduction map, chart-supported representatives, vanishing cycles), instantiated at the finitely indexed telescope of the full-level covering, with $S$ the image of the subgroup of inertia at $P$ on which the tame character at $\pi$ is trivial. It is used by the full-level results producing the comparison of Tate modules and the bound on the image of $\sigma-1$ on the $\lambda$-adic Tate module in terms of unipotent-fixed vectors.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_telescope_frame_of_semistableCovering.lean

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

theorem ModularCurve.FullLevel.telescope_frame_of_semistableCovering
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
    ∀ 𝒞 : ModularCurve.FullLevel.SemistableCovering q M' P W,
      𝒞.EquivClauses → 𝒞.W2Clauses π ι q → 𝒞.LevelPinClauses hle R₀ → 𝒞.InertiaClause π →
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
