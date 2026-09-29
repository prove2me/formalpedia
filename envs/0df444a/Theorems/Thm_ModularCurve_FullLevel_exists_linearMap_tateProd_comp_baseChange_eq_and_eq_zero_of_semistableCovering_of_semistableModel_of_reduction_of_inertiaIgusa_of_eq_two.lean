-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_exists_linearMap_tateProd_comp_baseChange_eq_and_eq_zero_of_semistableCovering_of_semistableModel_of_reduction_of_inertiaIgusa_of_eq_two
-- name    : ModularCurve.FullLevel.exists_linearMap_tateProd_comp_baseChange_eq_and_eq_zero_of_semistableCovering_of_semistableModel_of_reduction_of_inertiaIgusa_of_eq_two
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:35.562543+00:00
-- url     : https://prove2.me/theorems/fede26ae-908d-591f-852c-4f578cbcaf53
-- title:
--   Drinfeld specialisation sp₀ from a semistable covering, q=2
-- statement:
--   Fix primes $q$ (with $q=2$) and $\lambda\neq q$, and $M'\neq 0$ with $q\nmid M'$; assume `LevelAutInputs q M'` (each $\zeta\in$ `Idx q` and $\gamma\in\Gamma_0(M')$ admit an automorphism of `fieldBar q M'` over $\overline{\mathbb Q}$ satisfying `IsLevelAutBar`) and `GL2Laws q M'` (a monoid homomorphism $GL_2(\mathbb Z/q)\to\operatorname{End}(\mathrm{Jac}\,q\,M')$ inducing `slJac` on reductions of $\Gamma_0(M')$ and `diagJac` on the diagonal elements). Let $P$ be a valuation subring of $\overline{\mathbb Q}$ with $q$ a non-unit of $P$, let $W$ be the finset of places of `modularFunctionFieldC (ResidueField P) M'` consisting exactly of the supersingular places `ssPlaces q M'`, let $\pi\in P$ satisfy $\pi^{q^2-1}=q$, and let $\iota:\mathbb F_{q^2}\to\kappa(P)$ be a ring homomorphism, `CoordRing q (ResidueField P)` being a domain; assume `modularFunctionFieldBar M' ≤ fieldBar q M'` and fix a constant reduction $R_0$ of $P$ on `modularFunctionFieldBar M'` with values in `modularFunctionFieldC (ResidueField P) M'` whose residue computes coefficientwise residues of Laurent series over $P$. Give $\kappa(P)$ the $\mathbb F_{q^2}$-algebra structure from $\iota$, let $S$ be the set of semilinear automorphisms `arithmeticGalois (xHFunctionField (q^2*M') (levelH q M')) τ` for $\tau$ in the inertia subgroup of $P$ over $\mathbb Q$ with `tameCharacter π τ = 1`, and let $V^{\mathrm{inv}}$ be the $S$-invariants in the rational $\lambda$-adic Tate module of $\mathrm{Pic}^0(\overline{\mathbb Q},$ `fieldBar q M'`$)$. The assertion: for every semistable covering $\mathcal C$ of type `SemistableCovering q M' P W` satisfying the clauses `EquivClauses`, a Drinfeld clause `DrinfeldClause π ι η ζ s` with $\eta\in\{1,q\}$ for each $\zeta$ and $s\in W$, `IgusaUnipotentClause`, `LevelPinClauses hle R₀`, `InertiaClause π`, `WidthClause`, `GenusClause`, `DiscFibreClause`, `CurveClause`, `NaturalityClauses` and `InertiaIgusaInftyClause`, for every semistable model $M$ over $P$ of `fieldBar q M'` with components, charts, annuli and node places supplied by $\mathcal C$, for every descent datum for $M$, and for every $\mathbb Q_\lambda$-linear map $red$ from $V^{\mathrm{inv}}$ to the product over the telescope indices $i$ of the rational Tate modules of $\mathrm{Pic}^0(\kappa(P),\mathcal C.\mathrm{teleFbar}\,i)$ such that: (i) $red$ obeys the chartwise reduction law (for $v=1\otimes x$, each level $k$, each degree-zero divisor $D$ representing the $k$-th projection of $x$ and each decomposition $D=\sum_i D_i$ with $D_i$ supported in the $i$-th chart domain and of degree zero, $red\,v\,i=1\otimes y$ for some integral Tate vector $y$ whose $k$-th projection is the class of the pushforward of $D_i$ along the chart's place map); (ii) $red\,v=0$ exactly when $v$ lies in the $\mathbb Q_\lambda$-span of the elements $s\cdot w-w$ with $s\in S$; (iii) every $v=1\otimes x$ and every $k$ admit such a chart-supported degree-zero decomposition of a representative; (iv) every place in every chart domain is rational; there exists a $\mathbb Q_\lambda$-linear map $sp_0$ from the rational Tate module of $\mathrm{Jac}\,q\,M'$ to [`DrinfeldCurve.tateProd q (ResidueField P) lam ℚ_[lam] (Idx q × W)`](def/DrinfeldCurve_TateRep.html#L27) such that (A) for every $\tau$ in the inertia subgroup, every $\alpha\in\mathbb F_{q^2}^\times$ with $\iota(\alpha)=$ `tameCharacter π τ` and every $g\in GL_2(\mathbb Z/q)$ with $(g,\alpha)\in$ `hSubgroup q`, composing the base change of `tateGL2 g * tateGal τ` with $sp_0$ gives $sp_0$ followed by `tateProdRep ⟨(g,α),hg⟩`, and (B) $sp_0$ is injective on cuspidal vectors: if $v$ is annihilated by the base change of $\sum_{t\in\mathbb Z/q}$ `tateGL2 (unipotent t)` $\cdot$ `tateGL2 g` for every $g$, and $sp_0\,v=0$, then $v=0$.
--
--   This is the core specialisation step at the prime $q=2$: it converts the $\lambda$-adic reduction map attached to a semistable covering of the full-level modular curve, together with a semistable model and its descent, into a tame-inertia and $GL_2(\mathbb F_q)$-equivariant map from the Tate module of the full-level Jacobian to a product of Tate modules of Drinfeld curve Jacobians, injective on cuspidal vectors. It is used by the corresponding statement in which the reduction map is no longer hypothesised but constructed.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_exists_linearMap_tateProd_comp_baseChange_eq_and_eq_zero_of_semistableCovering_of_semistableModel_of_reduction_of_inertiaIgusa_of_eq_two.lean

import Definitions.Def_ModularCurve_FullLevelSemistableCoveringTelescope
import Definitions.Def_ModularCurve_FullLevelSemistableCoveringGuards
import Definitions.Def_ModularCurve_FullLevelSemistableCoveringNaturality
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_DrinfeldCurve_TateRep
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_SemistableModel
import Definitions.Def_ModularCurve_FullLevelSemistableCoveringInertiaIgusa

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve IsLocalRing
open scoped TensorProduct

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

theorem ModularCurve.FullLevel.exists_linearMap_tateProd_comp_baseChange_eq_and_eq_zero_of_semistableCovering_of_semistableModel_of_reduction_of_inertiaIgusa_of_eq_two
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
      𝒞.InertiaIgusaInftyClause →
      ∀ (M : AlgebraicCurve.SemistableModel P ↥(ModularCurve.FullLevel.fieldBar q M') 𝒞.sumFbar 𝒞.sumChart
          (fun e : CuspidalType.ProjLine q × ↥W => 𝒞.An e.1 e.2)
          (fun e => Sum.inl e.1) (fun e => Sum.inr e.2)
          (fun e => 𝒞.sumNode (Sum.inl e.1) e) (fun e => 𝒞.sumNode (Sum.inr e.2) e)) (_D : M.Descent),
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
      ∃ sp₀ : ModularCurve.RationalTateModule lam (ModularCurve.FullLevel.Jac q M') →ₗ[ℚ_[lam]]
          DrinfeldCurve.tateProd q (IsLocalRing.ResidueField P) lam ℚ_[lam] (ModularCurve.FullLevel.Idx q × ↥W),
        (∀ τ ∈ P.inertiaSubgroupIn ℚ, ∀ α : (GaloisField q 2)ˣ,
          ι (α : GaloisField q 2) = P.tameCharacter π τ →
            ∀ (g : CuspidalType.GL2 q) (hg : (g, α) ∈ DrinfeldCurve.hSubgroup q),
              sp₀ ∘ₗ (ModularCurve.FullLevel.tateGL2 q M' lam g *
                  ModularCurve.FullLevel.tateGal q M' lam τ).baseChange ℚ_[lam] =
                DrinfeldCurve.tateProdRep q (IsLocalRing.ResidueField P) lam ℚ_[lam]
                  (ModularCurve.FullLevel.Idx q × ↥W) ⟨(g, α), hg⟩ ∘ₗ sp₀) ∧
        (∀ v : ModularCurve.RationalTateModule lam (ModularCurve.FullLevel.Jac q M'),
          (∀ g : CuspidalType.GL2 q,
            (∑ t : ZMod q,
              (ModularCurve.FullLevel.tateGL2 q M' lam (CuspidalType.unipotent q t)).baseChange ℚ_[lam] *
                (ModularCurve.FullLevel.tateGL2 q M' lam g).baseChange ℚ_[lam]) v = 0) →
          sp₀ v = 0 → v = 0) := by sorry
