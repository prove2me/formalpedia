-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_eq_zero_of_cuspidalSpecialization_eq_zero_of_forall_sum_unipotent_eq_zero_of_semistableCovering_of_reduction
-- name    : ModularCurve.FullLevel.eq_zero_of_cuspidalSpecialization_eq_zero_of_forall_sum_unipotent_eq_zero_of_semistableCovering_of_reduction
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:33.630704+00:00
-- url     : https://prove2.me/theorems/953ff105-0df7-5e6f-972e-f0ef6bf7b289
-- title:
--   Injectivity of the cuspidal specialisation at full level q
-- statement:
--   **Setting.** Let $q\ge 5$ be a prime, let $M'\ge 1$ be an integer with $q\nmid M'$, and let $\lambda\neq q$ be a prime. Write $H=\ker\bigl((\mathbb Z/q^2M')^\times\to(\mathbb Z/q)^\times\bigr)$ for [`ModularCurve.FullLevel.levelH q M'`](def/ModularCurve_FullLevelJacobian.html#L22), the subgroup of units congruent to $1$ modulo $q$, and let $\bar F=$ [`ModularCurve.FullLevel.fieldBar q M'`](def/ModularCurve_FullLevelJacobian.html#L29) be the intermediate field of $\mathrm{LaurentSeries}(\overline{\mathbb Q})$ generated over $\overline{\mathbb Q}$ by the coefficientwise images of the $q$-expansion function field [`ModularCurve.xHFunctionField (q ^ 2 * M') H`](def/ModularCurve_XH.html#L79). Put `jacComp q M'` $=J_H(q^2M')$, and let `Jac q M'` be the group of functions from `Idx q`, the set of primitive $q$-th roots of unity in $\overline{\mathbb Q}$, to `jacComp q M'`.
--
--   Two structural hypotheses on the level action are imposed. `hLA` (`LevelAutInputs q M'`) asserts that for every $\zeta\in$ `Idx q` and every $\gamma\in\mathrm{SL}_2(\mathbb Z)$ lying in $\Gamma_0(M')$ there exists an automorphism of $\bar F$ over $\overline{\mathbb Q}$ satisfying the $q$-expansion condition `IsLevelAutBar q M' ζ γ`. `hGL` (`GL2Laws q M'`) asserts that there is a monoid homomorphism $G$ from $\mathrm{GL}_2(\mathbb Z/q)$ to the endomorphisms of `Jac q M'` with $G(\mathrm{redQ}\,\gamma)=$ `slJac q M' γ` for $\gamma\in\Gamma_0(M')$ and $G(\mathrm{diag}(1,d))=$ `diagJac q M' d` for $d\in(\mathbb Z/q)^\times$.
--
--   Further data: a valuation subring $P$ of $\overline{\mathbb Q}$ with $q$ a non-unit of $P$ (`hP`), with residue field $\kappa=\mathrm{ResidueField}\,P$; a finite set $W$ of places of `modularFunctionFieldC κ M'` which by `hW` consists exactly of the members of [`ModularCurve.ssPlaces q M' κ`](def/ModularCurve_SupersingularNodePlaces.html#L113), that is of the rational affine geometric places whose value of the geometric $j$-generator lies in `ssJSet q κ`; an element $\pi\in P$ with $\pi^{q^2-1}=q$; a ring homomorphism $\iota:\mathbb F_{q^2}\to\kappa$, used as the algebra structure of $\kappa$ over $\mathbb F_{q^2}$, under the assumption that [`DrinfeldCurve.CoordRing q κ`](def/DrinfeldCurve_CoordRing.html#L21) is a domain. Finally an inclusion `hle` of `modularFunctionFieldBar M'` in $\bar F$, and a constant reduction $R_0$ of `modularFunctionFieldBar M'` along $P$ with values in `modularFunctionFieldC κ M'`, i.e. a valuation subring of the source lying over $P$ together with a surjective residue homomorphism whose kernel is the maximal ideal, compatible with $P$ on constants, and a degree-preserving map on places compatible with pushforward of principal divisors. The hypothesis `hR₀` is a coefficientwise compatibility: for every Laurent series $y$ with coefficients in $P$ whose coefficientwise image in $\mathrm{LaurentSeries}(\overline{\mathbb Q})$ lies in `modularFunctionFieldBar M'`, that image lies in $R_0$.`integers`, and its $R_0$-residue, read as a Laurent series over $\kappa$, is the coefficientwise reduction of $y$ modulo the maximal ideal of $P$.
--
--   Two abbreviations are introduced. $S$ is the set of those semilinear automorphisms of $\bar F$ over $\overline{\mathbb Q}$ of the form [`ModularCurve.arithmeticGalois (xHFunctionField (q ^ 2 * M') H) τ`](def/ModularCurve_ArithmeticGalois.html#L54) (the coefficientwise action on Laurent series) for some $\tau$ in the inertia subgroup of $P$ inside $\mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q)$ with tame character $P.\mathrm{tameCharacter}\,\pi\,\tau=1$. And $V_{\mathrm{inv}}=\bigcap_{s\in S}\ker\bigl(\rho_\lambda(s)-1\bigr)$ inside $\mathbb Q_\lambda\otimes T_\lambda\bigl(\mathrm{Pic}^0_{\overline{\mathbb Q}}(\bar F)\bigr)$, where $\rho_\lambda$ is [`ModularCurve.rationalGaloisRep`](def/ModularCurve_JZeroTateModule.html#L48) for the action of the semilinear automorphism group.
--
--   **Assertion.** Let $\mathcal C$ be a semistable covering [`ModularCurve.FullLevel.SemistableCovering q M' P W`](def/ModularCurve_FullLevelSemistableCovering.html#L28) of $\bar F$ along $P$, with Igusa components indexed by $\ell\in\mathbb P^1(\mathbb Z/q)$ and supersingular components indexed by $s\in W$, and with its telescoped indexing `teleFbar`, `teleChart`, `eSS` over $\mathrm{Fin}\,\mathcal C.\mathrm{teleN}$. Assume the nine clauses of $\mathcal C$: `EquivClauses` (equivariance of the charts and annuli under the level automorphisms for $\gamma\in\Gamma_0(M')$, up to a permutation of $\mathbb P^1(\mathbb Z/q)$), `W2Clauses π ι q` (for all $\zeta$ and $s$ the Drinfeld clause with exponent $\eta=q$, identifying $\mathcal C.\mathrm{FSS}\,s$ with a quotient of the Drinfeld function field compatibly with the level and inertia actions, together with the Igusa unipotent clause for every $\zeta$), `LevelPinClauses hle R₀` (the two clauses pinning the reduction $R_0$ of the level-$M'$ function field to the supersingular and Igusa charts), `InertiaClause π` (inertia elements of tame character $1$ induce the identity on every chart and fix the place maps, chart domains and annulus parameters), `WidthClause ⟨π, hπP⟩` (every annulus modulus is a unit of $P$ times $\pi^{w}$ with $w\ge 1$), `GenusClause` (the genus identity relating the genus of $\bar F$ to the genera of the reduced components), `DiscFibreClause` (every chart has disc fibres), `CurveClause` (every reduced component is a curve over $\kappa$ and essentially of finite type over $\kappa$), and `NaturalityClauses` (the four compatibility clauses of the charts with inertia and with the level automorphisms, including the one at the line at infinity and the choice of a distinguished $\zeta_0$).
--
--   Let $\mathrm{red}:V_{\mathrm{inv}}\to\prod_i\mathbb Q_\lambda\otimes T_\lambda\bigl(\mathrm{Pic}^0_{\kappa}(\mathcal C.\mathrm{teleFbar}\,i)\bigr)$ be $\mathbb Q_\lambda$-linear and assume four laws for it. First, the chartwise reduction law: for $v\in V_{\mathrm{inv}}$ and $x$ in the integral Tate module with $v=1\otimes x$, for every $k$, every degree-zero divisor $D$ with $\mathrm{Pic}^0.\mathrm{mk}\,D$ equal to the $k$-th projection of $x$, and every decomposition $D=\sum_i D_i$ with each $D_i$ supported in the domain of the $i$-th chart and of degree zero, for each $i$ there is $y$ in the integral Tate module of $\mathrm{Pic}^0_\kappa(\mathcal C.\mathrm{teleFbar}\,i)$ with $\mathrm{red}\,v\,i=1\otimes y$ whose $k$-th projection is the class of any degree-zero divisor equal to the pushforward of $D_i$ along the chart's place map. Secondly, the kernel law: for $v\in V_{\mathrm{inv}}$, $\mathrm{red}\,v=0$ if and only if $v$ lies in the $\mathbb Q_\lambda$-span of the elements $\rho_\lambda(s)w-w$ with $s\in S$ and $w$ arbitrary. Thirdly, existence of chart-supported representatives: for $v\in V_{\mathrm{inv}}$, $x$ with $v=1\otimes x$ and every $k$ there exist $D$ of degree zero and a decomposition $D=\sum_iD_i$ with supports in the chart domains and each $D_i$ of degree zero, such that $\mathrm{Pic}^0.\mathrm{mk}\,D$ is the $k$-th projection of $x$. Fourthly, every place in the domain of every chart `teleChart i` is rational.
--
--   Assume further the span law for tame inertia on $V=\mathbb Q_\lambda\otimes T_\lambda(\mathrm{Jac}\,q\,M')$: for every $\tau$ in the inertia subgroup of $P$ in $\mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q)$ with $P.\mathrm{tameCharacter}\,\pi\,\tau=1$, the range of $(\mathrm{tateGal}\,q\,M'\,\lambda\,\tau)\otimes\mathbb Q_\lambda-1$ is contained in the $\mathbb Q_\lambda$-span of those $x$ for which there are $g\in\mathrm{GL}_2(\mathbb Z/q)$ and $v\in V$ fixed by $\mathrm{tateGL2}\,q\,M'\,\lambda\,(\mathrm{unipotent}\,t)$ for all $t\in\mathbb Z/q$ with $\mathrm{tateGL2}\,q\,M'\,\lambda\,(g)\,v=x$.
--
--   Assume given a $\mathbb Z_\lambda$-linear isomorphism $\Psi:T_\lambda(\mathrm{Jac}\,q\,M')\to\prod_{\zeta\in\mathrm{Idx}\,q}T_\lambda(\mathrm{jacComp}\,q\,M')$ subject to four laws: $\Psi$ is coordinatewise evaluation, in the sense that the $n$-th term of $\Psi x\,\zeta$ is the value at $\zeta$ of the $n$-th term of $x$; $\Psi$ intertwines the Galois action $\mathrm{tateGal}$ with $\sigma\mapsto\bigl(\zeta\mapsto \mathrm{JH.tateGaloisRep}\,(q^2M')\,H\,\lambda\,\sigma\ \text{applied to}\ \Psi x(\sigma^{-1}\zeta)\bigr)$; $\Psi$ intertwines $\mathrm{tateEnd}(\mathrm{slJac}\,\gamma)$ with the componentwise action of $\mathrm{JH.tateEnd}$ of `levelOp q M' ζ γ⁻¹`; and $\Psi$ intertwines $\mathrm{tateEnd}(\mathrm{diagJac}\,d)$ with the index permutation $\zeta\mapsto\zeta^{d^{-1}}$.
--
--   Assume given a $\mathbb Q_\lambda$-linear endomorphism $e_C$ of $\mathbb Q_\lambda\otimes T_\lambda(\mathrm{Jac}\,q\,M')$ acting as the identity on every $v$ annihilated by $\sum_{t\in\mathbb Z/q}\mathrm{tateGL2}(\mathrm{unipotent}\,t)\cdot\mathrm{tateGL2}(g)$ for all $g\in\mathrm{GL}_2(\mathbb Z/q)$ (base-changed to $\mathbb Q_\lambda$); a $\mathbb Q_\lambda$-linear map $e_{\mathrm{inv}}$ from $\mathbb Q_\lambda\otimes T_\lambda(\mathrm{jacComp}\,q\,M')$ to $V_{\mathrm{inv}}$ restricting to the identity on $V_{\mathrm{inv}}$, such that for every $v$ and every $\zeta$ the coordinate `ratCoord q M' lam Ψ ζ (eC v)` lies in $V_{\mathrm{inv}}$; and a family $\Phi$ of $\mathbb Q_\lambda$-linear maps, one for each $\zeta\in\mathrm{Idx}\,q$ and $s\in W$, from $\mathbb Q_\lambda\otimes T_\lambda\bigl(\mathrm{Pic}^0_\kappa(\mathcal C.\mathrm{teleFbar}(\mathcal C.\mathrm{eSS}\,s))\bigr)$ to $\mathbb Q_\lambda\otimes T_\lambda\bigl(\mathrm{Pic}^0_\kappa(\mathrm{drinfeldFunctionField}\,q\,\kappa)\bigr)$, each of which is assumed injective.
--
--   Then, for every $v\in\mathbb Q_\lambda\otimes T_\lambda(\mathrm{Jac}\,q\,M')$ such that $\bigl(\sum_{t\in\mathbb Z/q}\mathrm{tateGL2}\,q\,M'\,\lambda\,(\mathrm{unipotent}\,t)\cdot\mathrm{tateGL2}\,q\,M'\,\lambda\,(g)\bigr)v=0$ for every $g\in\mathrm{GL}_2(\mathbb Z/q)$, if $\mathrm{cuspidalSpecialization}\,q\,M'\,\lambda\,\kappa\,\Psi\,e_C\,V_{\mathrm{inv}}\,e_{\mathrm{inv}}\,\mathrm{red}\,\mathcal C.\mathrm{eSS}\,\Phi\,(v)=0$, then $v=0$. Here the cuspidal specialisation of $v$ is the family indexed by pairs $(\zeta,s)\in\mathrm{Idx}\,q\times W$ whose $(\zeta,s)$-entry is $1\otimes\Phi\,\zeta\,s$ applied to the $\mathcal C.\mathrm{eSS}\,s$-component of $\mathrm{red}\bigl(e_{\mathrm{inv}}(\mathrm{ratCoord}\,\zeta\,(e_Cv))\bigr)$.
--
--   This is the injectivity law for the cuspidal specialisation map attached to a semistable covering of the full-level-$q$ modular curve $X_H(q^2M')$ at a place $P$ of $\overline{\mathbb Q}$ above $q$: on the subspace of the $\lambda$-adic Tate module cut out by the vanishing of all operators $\sum_{t}u_t g$, the map assembled from the chartwise reductions and the Drinfeld-curve comparisons $\Phi$ has trivial kernel. It is used in [`ModularCurve.FullLevel.exists_linearMap_tateProd_comp_baseChange_eq_and_eq_zero_of_semistableCovering_of_semistableModel_of_reduction_of_inertiaIgusa`](thm.html#ModularCurve.FullLevel.exists_linearMap_tateProd_comp_baseChange_eq_and_eq_zero_of_semistableCovering_of_semistableModel_of_reduction_of_inertiaIgusa), where the cuspidal part of the Tate module is compared with the Tate module of the Drinfeld curve.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_eq_zero_of_cuspidalSpecialization_eq_zero_of_forall_sum_unipotent_eq_zero_of_semistableCovering_of_reduction.lean

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

theorem ModularCurve.FullLevel.eq_zero_of_cuspidalSpecialization_eq_zero_of_forall_sum_unipotent_eq_zero_of_semistableCovering_of_reduction
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
