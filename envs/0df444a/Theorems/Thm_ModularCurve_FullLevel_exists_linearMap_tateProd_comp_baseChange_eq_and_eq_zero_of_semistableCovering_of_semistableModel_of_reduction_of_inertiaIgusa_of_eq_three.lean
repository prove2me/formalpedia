-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_exists_linearMap_tateProd_comp_baseChange_eq_and_eq_zero_of_semistableCovering_of_semistableModel_of_reduction_of_inertiaIgusa_of_eq_three
-- name    : ModularCurve.FullLevel.exists_linearMap_tateProd_comp_baseChange_eq_and_eq_zero_of_semistableCovering_of_semistableModel_of_reduction_of_inertiaIgusa_of_eq_three
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:35.562543+00:00
-- url     : https://prove2.me/theorems/b4710f18-15b7-5eec-959d-701e0f9ab1ee
-- title:
--   Drinfeld specialisation sp₀ over a semistable covering, q=3
-- statement:
--   Fix a prime $q$ with $q=3$, a nonzero $M'$ with $q\nmid M'$, and a prime $\lambda\neq q$. Assume `LevelAutInputs q M'` (every $\zeta$ in `Idx q`, the set of primitive $q$-th roots of unity in $\overline{\mathbb Q}$, and every $\gamma\in\Gamma_0(M')$ admit an automorphism of `fieldBar q M'` over $\overline{\mathbb Q}$ realising the level action) and `GL2Laws q M'` (a monoid homomorphism $GL_2(\mathbb Z/q)\to\operatorname{End}(\mathrm{Jac}\,q\,M')$ agreeing with the $\Gamma_0(M')$-action and with the diagonal action). Let $P$ be a valuation subring of $\overline{\mathbb Q}$ with $q$ a nonunit of $P$, $W$ the finset of places of `modularFunctionFieldC (ResidueField P) M'` consisting exactly of the supersingular places, $\pi\in P$ with $\pi^{q^2-1}=q$, and $\iota:\mathbb F_{q^2}\to\kappa(P)$ a ring homomorphism, the Drinfeld coordinate ring over $\kappa(P)$ being a domain; let `hle` be the inclusion of `modularFunctionFieldBar M'` in `fieldBar q M'`, and $R_0$ a constant reduction along $P$ from `modularFunctionFieldBar M'` to `modularFunctionFieldC (ResidueField P) M'` whose residue, by hypothesis `hR₀`, computes the coefficientwise reduction of any Laurent series over $P$ lying in `modularFunctionFieldBar M'`. Put $S$ for the set of semilinear automorphisms `arithmeticGalois (xHFunctionField (q^2*M') (levelH q M')) τ` with $\tau$ in the inertia subgroup of $P$ over $\mathbb Q$ and tame character $P.\mathrm{tameCharacter}\,\pi\,\tau=1$, and $V^{\mathrm{inv}}$ for the $S$-invariants in $\mathbb Q_\lambda\otimes T_\lambda\mathrm{Pic}^0(\overline{\mathbb Q},\mathrm{fieldBar}\,q\,M')$. Then for every semistable covering $\mathcal C$ of `fieldBar q M'` along $P$ with node set $W$ satisfying its equivalence clauses, a Drinfeld clause with inertia exponent $\eta\in\{1,q\}$ chosen at each pair $(\zeta,s)$, the Igusa unipotent clauses, the level-pinning clauses for `hle` and $R_0$, the inertia clause for $\pi$, the width clause for $\pi$, and the genus, discrete-fibre, curve, naturality and inertia–Igusa-at-infinity clauses; for every semistable model $M$ over $P$ built from the telescoped components, charts and annuli of $\mathcal C$ together with a descent of $M$; and for every $\mathbb Q_\lambda$-linear map $red$ from $V^{\mathrm{inv}}$ to the product over $i<\mathcal C.\mathrm{teleN}$ of $\mathbb Q_\lambda\otimes T_\lambda\mathrm{Pic}^0(\kappa(P),\mathcal C.\mathrm{teleFbar}\,i)$ such that: (i) $red$ obeys the chartwise reduction law (if $v$ is represented by $1\otimes x$ with $x$ in the integral Tate module, the $k$-th projection of $x$ is the class of a degree-zero divisor $D=\sum_i D_i$ with each $D_i$ supported in the $i$-th chart domain and of degree zero, then $red\,v\,i=1\otimes y$ for some integral $y$ whose $k$-th projection is the class of the `placeMap`-push-forward of $D_i$); (ii) $red\,v=0$ if and only if $v$ lies in the $\mathbb Q_\lambda$-span of the elements $s\cdot w-w$ for $s\in S$; (iii) every $v\in V^{\mathrm{inv}}$ with integral representative admits, at each level $k$, a degree-zero divisor representative decomposed into chart-supported degree-zero pieces; and (iv) all places in all chart domains are rational; there exists a $\mathbb Q_\lambda$-linear map $sp_0$ from $\mathbb Q_\lambda\otimes T_\lambda(\mathrm{Jac}\,q\,M')$ to [`DrinfeldCurve.tateProd q (ResidueField P) lam ℚ_[lam] (Idx q × W)`](def/DrinfeldCurve_TateRep.html#L27) such that, firstly, for every $\tau$ in the inertia subgroup and every $\alpha\in\mathbb F_{q^2}^{\times}$ with $\iota(\alpha)=P.\mathrm{tameCharacter}\,\pi\,\tau$ and every $g\in GL_2(\mathbb Z/q)$ with $(g,\alpha)$ in [`DrinfeldCurve.hSubgroup q`](def/DrinfeldCurve_CoordRing.html#L276), composing the base change of `tateGL2 g * tateGal τ` with $sp_0$ gives $sp_0$ followed by `tateProdRep ⟨(g,α),hg⟩`; and secondly, $sp_0$ is injective on cuspidal vectors: if $v$ satisfies $\sum_{t\in\mathbb Z/q}\mathrm{tateGL2}(\mathrm{unipotent}\,t)\,\mathrm{tateGL2}(g)\,v=0$ for all $g$ and $sp_0v=0$, then $v=0$.
--
--   This is the covering-level Drinfeld specialisation of the full-level Jacobian's $\lambda$-adic Tate module in the case $q=3$: it converts a reduction map on the tame-inertia invariants, together with the clauses of a semistable covering and a semistable model with descent, into an equivariant map $sp_0$ to the product of Drinfeld-curve Tate modules that is injective on cuspidal vectors. It is the input to [`ModularCurve.FullLevel.exists_linearMap_tateProd_comp_baseChange_eq_and_eq_zero_of_semistableCovering_of_semistableModel_of_inertiaIgusa_of_eq_three`](thm.html#ModularCurve.FullLevel.exists_linearMap_tateProd_comp_baseChange_eq_and_eq_zero_of_semistableCovering_of_semistableModel_of_inertiaIgusa_of_eq_three), where the reduction-map hypotheses are discharged.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_exists_linearMap_tateProd_comp_baseChange_eq_and_eq_zero_of_semistableCovering_of_semistableModel_of_reduction_of_inertiaIgusa_of_eq_three.lean

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

theorem ModularCurve.FullLevel.exists_linearMap_tateProd_comp_baseChange_eq_and_eq_zero_of_semistableCovering_of_semistableModel_of_reduction_of_inertiaIgusa_of_eq_three
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
