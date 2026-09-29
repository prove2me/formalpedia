-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_eq_zero_of_cuspidalSpecialization_eq_zero_of_forall_sum_unipotent_eq_zero_of_semistableCovering_of_reduction_of_eq_two
-- name    : ModularCurve.FullLevel.eq_zero_of_cuspidalSpecialization_eq_zero_of_forall_sum_unipotent_eq_zero_of_semistableCovering_of_reduction_of_eq_two
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:33.630704+00:00
-- url     : https://prove2.me/theorems/006bd1d6-a31b-5b18-ab26-2b774056a326
-- title:
--   Injectivity of cuspidal specialisation along a semistable covering, q=2
-- statement:
--   Throughout, $q$ is a prime with $q = 2$ (kept symbolic), $M' \ge 1$ is an integer with $q \nmid M'$, and $\lambda$ is a prime with $\lambda \ne q$. The curve side is the level-$H$ function field of level $q^2M'$: [`ModularCurve.FullLevel.levelH q M'`](def/ModularCurve_FullLevelJacobian.html#L22) is the kernel of the reduction map $(\mathbb{Z}/q^2M')^\times \to (\mathbb{Z}/q)^\times$, i.e. the units congruent to $1$ modulo $q$, [`ModularCurve.FullLevel.fieldBar q M'`](def/ModularCurve_FullLevelJacobian.html#L29) is the corresponding function field base-changed coefficientwise to $\overline{\mathbb{Q}}$ inside $\overline{\mathbb{Q}}((T))$, [`ModularCurve.FullLevel.jacComp q M'`](def/ModularCurve_FullLevelJacobian.html#L32) is its Jacobian $J_H(q^2M')$, [`ModularCurve.FullLevel.Idx q`](def/ModularCurve_FullLevelJacobian.html#L40) is the set of primitive $q$-th roots of unity in $\overline{\mathbb{Q}}$, and [`ModularCurve.FullLevel.Jac q M'`](def/ModularCurve_FullLevelJacobian.html#L85) is the product $\mathrm{Idx}(q) \to J_H(q^2M')$, carrying the Galois action `galJac` (twisting the index by $\sigma^{-1}$), the $\mathrm{SL}_2(\mathbb{Z})$-action `slJac` through the level automorphisms `levelAutBar`, and the diagonal action `diagJac` permuting indices by $\zeta \mapsto \zeta^{d^{-1}}$; `tateGal`, `tateEnd`, `tateGL2` are the induced operators on $T_\lambda(\mathrm{Jac})$, the last through a monoid homomorphism $\mathrm{GL}_2(\mathbb{Z}/q) \to \mathrm{End}(\mathrm{Jac})$ selected by `GL2Laws`.
--
--   The data are: the hypothesis `hLA` (`LevelAutInputs q M'`), asserting that for every $\zeta \in \mathrm{Idx}(q)$ and every $\gamma \in \Gamma_0(M')$ a level automorphism in the sense of `IsLevelAutBar` exists; the hypothesis `hGL` (`GL2Laws q M'`), asserting the existence of a monoid homomorphism $\mathrm{GL}_2(\mathbb{Z}/q) \to \mathrm{End}(\mathrm{Jac}\,(q,M'))$ carrying the reduction of each $\gamma \in \Gamma_0(M')$ to `slJac q M' γ` and each $\mathrm{diag}(1,d)$ to `diagJac q M' d`; a valuation subring $P$ of $\overline{\mathbb{Q}}$ with $q$ a non-unit of $P$ (`hP`), with residue field $\kappa(P)$; a finite set $W$ of places of $\kappa(P)$-modular function field `modularFunctionFieldC (ResidueField P) M'` which by `hW` is exactly the set of supersingular places, i.e. those places that are rational, affine geometric, and whose value at the geometric $j$-generator lies in the supersingular $j$-set over $\kappa(P)$; an element $\pi \in \overline{\mathbb{Q}}$ with $\pi^{q^2-1} = q$ and $\pi \in P$; a ring homomorphism $\iota : \mathbb{F}_{q^2} \to \kappa(P)$, through which $\kappa(P)$ is made an $\mathbb{F}_{q^2}$-algebra, the Drinfeld coordinate ring over $\kappa(P)$ being assumed to be a domain; the inclusion `hle` of the base-changed full modular function field of level $M'$ into `fieldBar q M'`; and a constant reduction $R_0$ from $P$ on that level-$M'$ field to `modularFunctionFieldC (ResidueField P) M'`, subject to the coefficientwise compatibility `hR₀`: for every Laurent series $y$ over $P$ whose coefficientwise image in $\overline{\mathbb{Q}}((T))$ lies in the level-$M'$ field, that element lies in $R_0$.integers and its $R_0$-residue, read as a Laurent series over $\kappa(P)$, is the coefficientwise reduction of $y$.
--
--   Two objects are then introduced. $S$ is the set of those semilinear automorphisms of `fieldBar q M'` over $\overline{\mathbb{Q}}$ of the form `arithmeticGalois` (coefficientwise action on Laurent series) of some $\tau$ in the inertia subgroup of $P$ over $\mathbb{Q}$ with $P$-tame character $P.\mathrm{tameCharacter}\,\pi\,\tau = 1$. And $V_{\mathrm{inv}}$ is the $\mathbb{Q}_\lambda$-subspace $\bigcap_{s \in S} \ker(s - 1)$ of the rational $\lambda$-adic Tate module of $\mathrm{Pic}^0$ of `fieldBar q M'` over $\overline{\mathbb{Q}}$, the action being `rationalGaloisRep`.
--
--   The assertion is made for every semistable covering $\mathcal{C}$ of `fieldBar q M'` along $P$ with supersingular index set $W$ (Igusa charts $C^{\mathrm{Ig}}_\ell$ indexed by $\ell \in \mathbb{P}^1(\mathbb{Z}/q)$, supersingular charts $C^{\mathrm{SS}}_s$ indexed by $s \in W$, annuli joining them, with the attachment and partition axioms of the structure), subject to ten clauses: `𝒞.EquivClauses` (for each $\zeta$ and each $\gamma \in \Gamma_0(M')$ a permutation of $\mathbb{P}^1(\mathbb{Z}/q)$ matching the pullbacks of the charts and annuli along `levelAutBar q M' ζ γ`); a per-point Drinfeld clause, namely that for every $\zeta \in \mathrm{Idx}(q)$ and every $s \in W$ there is an exponent $\eta \in \{1, q\}$ with `𝒞.DrinfeldClause π ι η ζ s` (an identification of the supersingular residue field $F^{\mathrm{SS}}_s$ with a $C$-fixed subfield of the Drinfeld function field over $\kappa(P)$, equivariant for the level automorphisms and for inertia via the tame character, with the $\eta$-th power hedge on the diagonal part); `𝒞.IgusaUnipotentClause ζ` for every $\zeta$ (for $\gamma \in \Gamma_0(M')$ with unipotent reduction, `levelAutBar q M' ζ γ⁻¹` induces the identity on the Igusa chart at $\ell = \infty$); `𝒞.LevelPinClauses hle R₀` (pinning the supersingular and Igusa chart residues against $R_0$ and the places of $W$); `𝒞.InertiaClause π` (inertia of tame character $1$ acts trivially on all charts, place maps, chart domains and annulus parameters); `𝒞.WidthClause ⟨π, hπP⟩` (each annulus modulus is a unit times a positive power of $\pi$); `𝒞.GenusClause` (the genus identity for the covering); `𝒞.DiscFibreClause`; `𝒞.CurveClause` (each residue function field is a curve over $\kappa(P)$ and essentially of finite type); and `𝒞.NaturalityClauses`.
--
--   Next, for every $\mathbb{Q}_\lambda$-linear map $\mathrm{red} : V_{\mathrm{inv}} \to \prod_i \mathbb{Q}_\lambda \otimes T_\lambda(\mathrm{Pic}^0_{\kappa(P)}(\mathcal{C}.\mathrm{teleFbar}\, i))$, indexed by the enumeration of $\mathbb{P}^1(\mathbb{Z}/q) \sqcup W$ by `Fin 𝒞.teleN`, four hypotheses on $\mathrm{red}$ are imposed: the chartwise reduction law, namely that for $v \in V_{\mathrm{inv}}$ and $x$ in the integral Tate module with $v = 1 \otimes x$, for every level $k$, every degree-zero divisor $D$ with $[D] = \mathrm{proj}_k(x)$ and every decomposition $D = \sum_i D_i$ with each $D_i$ supported in the domain of $\mathcal{C}.\mathrm{teleChart}\,i$ and of degree zero, there is $y \in T_\lambda(\mathrm{Pic}^0_{\kappa(P)}(\mathcal{C}.\mathrm{teleFbar}\,i))$ with $\mathrm{red}(v)_i = 1 \otimes y$ and $\mathrm{proj}_k(y) = [E]$ for every degree-zero divisor $E$ equal to the pushforward of $D_i$ along the chart's place map; the kernel law, that $\mathrm{red}(v) = 0$ holds if and only if $v$ lies in the $\mathbb{Q}_\lambda$-span of $\{s w - w : s \in S,\ w \text{ arbitrary}\}$; the existence of chart-supported representatives, that for $v \in V_{\mathrm{inv}}$ with $v = 1 \otimes x$ and every $k$ there are $D$, a proof that $D$ has degree zero, and $(D_i)_i$ with $[D] = \mathrm{proj}_k(x)$, $D = \sum_i D_i$, each $D_i$ supported in the domain of the $i$-th chart and of degree zero; and rationality, that every place in the domain of every $\mathcal{C}.\mathrm{teleChart}\,i$ is rational.
--
--   Further assumed is the toric span law at inertia: for every $\tau$ in the inertia subgroup of $P$ over $\mathbb{Q}$ with tame character $1$, the image of $(\mathrm{tateGal}\,\tau) \otimes 1 - 1$ on $\mathbb{Q}_\lambda \otimes T_\lambda(\mathrm{Jac}\,(q,M'))$ is contained in the $\mathbb{Q}_\lambda$-span of those $x$ for which there exist $g \in \mathrm{GL}_2(\mathbb{Z}/q)$ and a vector $v$ fixed by all the unipotent operators `tateGL2 q M' lam (CuspidalType.unipotent q t)`, $t \in \mathbb{Z}/q$, with $x = \mathrm{tateGL2}(g)\,v$.
--
--   Next, a $\mathbb{Z}_\lambda$-linear isomorphism $\Psi : T_\lambda(\mathrm{Jac}\,(q,M')) \xrightarrow{\sim} (\mathrm{Idx}(q) \to T_\lambda(J_H(q^2M')))$ is given, subject to four laws: coordinatewise description, that the $n$-th component of $\Psi(x)_\zeta$ is the value at $\zeta$ of the $n$-th component of $x$; Galois equivariance, $\Psi(\mathrm{tateGal}(\sigma)x)_\zeta = \mathrm{tateGaloisRep}(\sigma)\,\Psi(x)_{\sigma^{-1}\zeta}$ for the $J_H(q^2M')$-representation; $\mathrm{SL}_2(\mathbb{Z})$-equivariance, $\Psi(\mathrm{tateEnd}(\mathrm{slJac}\,\gamma)x)_\zeta = \mathrm{tateEnd}(\mathrm{levelOp}\,\zeta\,\gamma^{-1})\,\Psi(x)_\zeta$; and the diagonal law, $\Psi(\mathrm{tateEnd}(\mathrm{diagJac}\,d)x)_\zeta = \Psi(x)_{\zeta^{d^{-1}}}$.
--
--   Finally: a $\mathbb{Q}_\lambda$-linear endomorphism $e_C$ of $\mathbb{Q}_\lambda \otimes T_\lambda(\mathrm{Jac}\,(q,M'))$ acting as the identity on every vector $v$ satisfying the cuspidality condition that $\bigl(\sum_{t \in \mathbb{Z}/q} U_t T_g\bigr) v = 0$ for all $g \in \mathrm{GL}_2(\mathbb{Z}/q)$, where $U_t$ and $T_g$ are the base-changed operators `tateGL2 q M' lam (CuspidalType.unipotent q t)` and `tateGL2 q M' lam g`; a $\mathbb{Q}_\lambda$-linear map $e_{\mathrm{inv}}$ from $\mathbb{Q}_\lambda \otimes T_\lambda(J_H(q^2M'))$ to $V_{\mathrm{inv}}$ restricting to the identity on $V_{\mathrm{inv}}$; the hypothesis that for every $v$ and every $\zeta$ the $\zeta$-coordinate `ratCoord q M' lam Ψ ζ (eC v)` lies in $V_{\mathrm{inv}}$; and a family $\Phi$ of $\mathbb{Q}_\lambda$-linear maps $\Phi_{\zeta,s}$ from $\mathbb{Q}_\lambda \otimes T_\lambda(\mathrm{Pic}^0_{\kappa(P)}(\mathcal{C}.\mathrm{teleFbar}(\mathcal{C}.\mathrm{eSS}\,s)))$ to $\mathbb{Q}_\lambda \otimes T_\lambda(\mathrm{Pic}^0_{\kappa(P)}(\text{Drinfeld function field over } \kappa(P)))$, indexed by $\zeta \in \mathrm{Idx}(q)$ and $s \in W$, each of which is injective.
--
--   Under all of these hypotheses the conclusion is: for every $v \in \mathbb{Q}_\lambda \otimes T_\lambda(\mathrm{Jac}\,(q,M'))$, if $\bigl(\sum_{t \in \mathbb{Z}/q} U_t T_g\bigr) v = 0$ for all $g \in \mathrm{GL}_2(\mathbb{Z}/q)$ and if the cuspidal specialisation of $v$ vanishes — that is, the family indexed by $(\zeta, s) \in \mathrm{Idx}(q) \times W$ whose $(\zeta,s)$-entry is $1 \otimes \Phi_{\zeta,s}\bigl(\mathrm{red}(e_{\mathrm{inv}}(\mathrm{ratCoord}\,\zeta\,(e_C v)))_{\mathcal{C}.\mathrm{eSS}\,s}\bigr)$ is zero — then $v = 0$.
--
--   This is the injectivity statement for the specialisation of the cuspidal part of the $\lambda$-adic Tate module of the full-level Jacobian onto the supersingular (Drinfeld) components of the reduction at a place above $q$, in the case $q = 2$, where the Drinfeld comparison is supplied point by point with a hedged exponent $\eta \in \{1, q\}$. It is the form of the toric/cuspidal dichotomy used at $q=2$, and it is invoked by [`ModularCurve.FullLevel.exists_linearMap_tateProd_comp_baseChange_eq_and_eq_zero_of_semistableCovering_of_semistableModel_of_reduction_of_inertiaIgusa_of_eq_two`](thm.html#ModularCurve.FullLevel.exists_linearMap_tateProd_comp_baseChange_eq_and_eq_zero_of_semistableCovering_of_semistableModel_of_reduction_of_inertiaIgusa_of_eq_two).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_eq_zero_of_cuspidalSpecialization_eq_zero_of_forall_sum_unipotent_eq_zero_of_semistableCovering_of_reduction_of_eq_two.lean

import Definitions.Def_ModularCurve_FullLevelSemistableCoveringTelescope
import Definitions.Def_ModularCurve_FullLevelSemistableCoveringGuards
import Definitions.Def_ModularCurve_FullLevelSemistableCoveringNaturality
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_DrinfeldCurve_TateRep
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_ModularCurve_FullLevelCuspidalSpecialization

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve IsLocalRing
open scoped TensorProduct

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable
set_option maxHeartbeats 400000 in

theorem ModularCurve.FullLevel.eq_zero_of_cuspidalSpecialization_eq_zero_of_forall_sum_unipotent_eq_zero_of_semistableCovering_of_reduction_of_eq_two
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

      (∀ τ ∈ P.inertiaSubgroupIn ℚ, P.tameCharacter π τ = 1 →
        LinearMap.range ((ModularCurve.FullLevel.tateGal q M' lam τ).baseChange ℚ_[lam] - 1) ≤
          Submodule.span ℚ_[lam] {x : ModularCurve.RationalTateModule lam (ModularCurve.FullLevel.Jac q M') |
            ∃ (g : CuspidalType.GL2 q) (v : ModularCurve.RationalTateModule lam (ModularCurve.FullLevel.Jac q M')),
              (∀ t : ZMod q,
                (ModularCurve.FullLevel.tateGL2 q M' lam (CuspidalType.unipotent q t)).baseChange ℚ_[lam] v = v) ∧
              (ModularCurve.FullLevel.tateGL2 q M' lam g).baseChange ℚ_[lam] v = x}) →

      ∀ (Ψ : TateModule lam (ModularCurve.FullLevel.Jac q M') ≃ₗ[ℤ_[lam]]
          (ModularCurve.FullLevel.Idx q → TateModule lam (ModularCurve.FullLevel.jacComp q M'))),
      (∀ (x : TateModule lam (ModularCurve.FullLevel.Jac q M')) (ζ : ModularCurve.FullLevel.Idx q) (n : ℕ),
        ((Ψ x ζ : TateModule lam (ModularCurve.FullLevel.jacComp q M')) : ℕ → ModularCurve.FullLevel.jacComp q M') n =
          (((x : TateModule lam (ModularCurve.FullLevel.Jac q M')) : ℕ → ModularCurve.FullLevel.Jac q M') n).eval ζ) →
      (∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (x : TateModule lam (ModularCurve.FullLevel.Jac q M'))
          (ζ : ModularCurve.FullLevel.Idx q),
        Ψ (ModularCurve.FullLevel.tateGal q M' lam σ x) ζ =
          ModularCurve.JH.tateGaloisRep (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M') lam σ (Ψ x (σ⁻¹ • ζ))) →
      (∀ (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) (x : TateModule lam (ModularCurve.FullLevel.Jac q M'))
          (ζ : ModularCurve.FullLevel.Idx q),
        Ψ (ModularCurve.FullLevel.tateEnd q M' lam (ModularCurve.FullLevel.slJac q M' γ) x) ζ =
          ModularCurve.JH.tateEnd (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M') lam
            (ModularCurve.FullLevel.levelOp q M' ζ γ⁻¹) (Ψ x ζ)) →
      (∀ (d : (ZMod q)ˣ) (x : TateModule lam (ModularCurve.FullLevel.Jac q M')) (ζ : ModularCurve.FullLevel.Idx q),
        Ψ (ModularCurve.FullLevel.tateEnd q M' lam (ModularCurve.FullLevel.diagJac q M' d) x) ζ = Ψ x (ζ.pow d⁻¹)) →
      ∀ (eC : ModularCurve.RationalTateModule lam (ModularCurve.FullLevel.Jac q M') →ₗ[ℚ_[lam]]
          ModularCurve.RationalTateModule lam (ModularCurve.FullLevel.Jac q M')),
      (∀ v : ModularCurve.RationalTateModule lam (ModularCurve.FullLevel.Jac q M'),
        (∀ g : CuspidalType.GL2 q,
          (∑ t : ZMod q,
            (ModularCurve.FullLevel.tateGL2 q M' lam (CuspidalType.unipotent q t)).baseChange ℚ_[lam] *
              (ModularCurve.FullLevel.tateGL2 q M' lam g).baseChange ℚ_[lam]) v = 0) →
        eC v = v) →
      ∀ (eInv : ModularCurve.RationalTateModule lam (ModularCurve.FullLevel.jacComp q M') →ₗ[ℚ_[lam]] ↥Vinv),
      (∀ w : ↥Vinv, eInv (w : ModularCurve.RationalTateModule lam (ModularCurve.FullLevel.jacComp q M')) = w) →
      (∀ (v : ModularCurve.RationalTateModule lam (ModularCurve.FullLevel.Jac q M')) (ζ : ModularCurve.FullLevel.Idx q),
        ModularCurve.FullLevel.ratCoord q M' lam Ψ ζ (eC v) ∈ Vinv) →
      ∀ (Φ : (ζ : ModularCurve.FullLevel.Idx q) → (s : ↥W) →
          (ModularCurve.RationalTateModule lam (Pic0 (IsLocalRing.ResidueField P) (𝒞.teleFbar (𝒞.eSS s))) →ₗ[ℚ_[lam]]
            ModularCurve.RationalTateModule lam
              (Pic0 (IsLocalRing.ResidueField P)
                (DrinfeldCurve.drinfeldFunctionField q (IsLocalRing.ResidueField P))))),
      (∀ (ζ : ModularCurve.FullLevel.Idx q) (s : ↥W), Function.Injective (Φ ζ s)) →
      ∀ v : ModularCurve.RationalTateModule lam (ModularCurve.FullLevel.Jac q M'),
        (∀ g : CuspidalType.GL2 q,
          (∑ t : ZMod q,
            (ModularCurve.FullLevel.tateGL2 q M' lam (CuspidalType.unipotent q t)).baseChange ℚ_[lam] *
              (ModularCurve.FullLevel.tateGL2 q M' lam g).baseChange ℚ_[lam]) v = 0) →
        ModularCurve.FullLevel.cuspidalSpecialization q M' lam (IsLocalRing.ResidueField P)
            Ψ eC Vinv eInv red 𝒞.eSS Φ v = 0 →
        v = 0 := by sorry
