-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_eq_zero_of_cuspidalSpecialization_eq_zero_of_forall_sum_unipotent_eq_zero_of_semistableCovering_of_reduction_of_eq_three
-- name    : ModularCurve.FullLevel.eq_zero_of_cuspidalSpecialization_eq_zero_of_forall_sum_unipotent_eq_zero_of_semistableCovering_of_reduction_of_eq_three
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:33.630704+00:00
-- url     : https://prove2.me/theorems/ce532154-8b46-583f-aa8d-284121ae6fc2
-- title:
--   Cuspidal specialisation is injective at full level, q=3
-- statement:
--   Throughout, $q$ is a prime with $q = 3$, $M'$ is a nonzero natural number with $q \nmid M'$, and $\lambda$ is a prime with $q \neq \lambda$. Two structural inputs at level $M'$ are assumed: [`ModularCurve.FullLevel.LevelAutInputs q M'`](def/ModularCurve_FullLevelJacobian.html#L220), which asserts that for every $\zeta$ in [`ModularCurve.FullLevel.Idx q`](def/ModularCurve_FullLevelJacobian.html#L40) (the primitive $q$-th roots of unity in $\overline{\mathbb{Q}}$) and every $\gamma \in \Gamma_0(M') \subseteq \mathrm{SL}_2(\mathbb{Z})$ there is an $\overline{\mathbb{Q}}$-algebra automorphism $\tau$ of [`ModularCurve.FullLevel.fieldBar q M'`](def/ModularCurve_FullLevelJacobian.html#L29) satisfying the predicate `IsLevelAutBar q M' ζ γ`; and [`ModularCurve.FullLevel.GL2Laws q M'`](def/ModularCurve_FullLevelJacobian.html#L255), which asserts the existence of a monoid homomorphism $G$ from $\mathrm{GL}_2(\mathbb{Z}/q)$ to the additive endomorphisms of [`ModularCurve.FullLevel.Jac q M'`](def/ModularCurve_FullLevelJacobian.html#L85) with $G(\mathrm{red}_q\gamma) =$ `slJac q M' γ` for $\gamma \in \Gamma_0(M')$ and $G($`diagOneElem q d`$) =$ `diagJac q M' d` for $d \in (\mathbb{Z}/q)^\times$. Here `fieldBar q M'` is the intermediate field `xHFunctionFieldBar (q ^ 2 * M') (levelH q M')` of $\mathrm{LaurentSeries}(\overline{\mathbb{Q}})$ over $\overline{\mathbb{Q}}$, with `levelH q M'` the kernel of the reduction $(\mathbb{Z}/q^2M')^\times \to (\mathbb{Z}/q)^\times$; `jacComp q M'` is `JH (q ^ 2 * M') (levelH q M')`, which is the degree-zero Picard group $\mathrm{Pic}^0(\overline{\mathbb{Q}},$`fieldBar q M'`$)$, and `Jac q M'` is the product of copies of `jacComp q M'` indexed by `Idx q`.
--
--   Further data: a valuation subring $P$ of $\overline{\mathbb{Q}}$ with `P.LiesOverPrime q`, i.e. $q$ lies in the nonunits of $P$; a finite set $W$ of places of `modularFunctionFieldC (ResidueField P) M'` over the residue field $\kappa(P) =$ `ResidueField P`, characterised by `hW` as consisting exactly of the places satisfying `IsSupersingularPlace q M' (ResidueField P)`, i.e. $W$ is precisely [`ModularCurve.ssPlaces q M' (ResidueField P)`](def/ModularCurve_SupersingularNodePlaces.html#L113); an element $\pi \in \overline{\mathbb{Q}}$ with $\pi^{q^2-1} = q$ and $\pi \in P$; a ring homomorphism $\iota$ from the Galois field `GaloisField q 2` $= \mathbb{F}_{q^2}$ to $\kappa(P)$, used as the algebra structure making $\kappa(P)$ an $\mathbb{F}_{q^2}$-algebra, and the assumption that [`DrinfeldCurve.CoordRing q (ResidueField P)`](def/DrinfeldCurve_CoordRing.html#L21) is a domain; the inclusion `hle` of `modularFunctionFieldBar M'` into `fieldBar q M'`; and a constant reduction $R_0$ of `modularFunctionFieldBar M'` along $P$ with values in `modularFunctionFieldC (ResidueField P) M'`, that is, a valuation subring $R_0.\mathrm{integers}$ of the source, a surjective residue homomorphism onto the target with kernel the maximal ideal, a map on places preserving degrees, and the compatibility axioms of [`AlgebraicCurve.ConstantReduction`](def/AlgebraicCurve_ConstantReduction.html#L17). The hypothesis `hR₀` requires $R_0$ to compute coefficientwise reduction: for every Laurent series $y$ over $P$ whose image under coefficientwise application of the inclusion $P \hookrightarrow \overline{\mathbb{Q}}$ lies in `modularFunctionFieldBar M'`, that image lies in $R_0.\mathrm{integers}$ and its $R_0$-residue, read as a Laurent series over $\kappa(P)$, equals the coefficientwise reduction of $y$ under $P \to \kappa(P)$.
--
--   Two derived objects are fixed. First, $S$ is the set of those semilinear automorphisms of `fieldBar q M'` over $\overline{\mathbb{Q}}$ (elements of `SemilinearAut`, i.e. pairs of ring automorphisms compatible with the structure map) of the form [`ModularCurve.arithmeticGalois (xHFunctionField (q ^ 2 * M') (levelH q M')) τ`](def/ModularCurve_ArithmeticGalois.html#L54), the coefficientwise action of $\tau$, for $\tau$ in the inertia subgroup `P.inertiaSubgroupIn ℚ` with tame character `P.tameCharacter π τ = 1`. Second, $V_{\mathrm{inv}}$ is the intersection over $s \in S$ of the kernels of $s - 1$ acting on the rational Tate module $\mathbb{Q}_\lambda \otimes_{\mathbb{Z}_\lambda} T_\lambda \mathrm{Pic}^0(\overline{\mathbb{Q}},$`fieldBar q M'`$)$ through [`ModularCurve.rationalGaloisRep`](def/ModularCurve_JZeroTateModule.html#L48); here $T_\lambda M$ consists of the sequences $(x_n)$ in $M$ with $\lambda^n x_n = 0$ and $\lambda x_{n+1} = x_n$.
--
--   The assertion is made for every semistable covering $\mathcal{C}$ of type [`ModularCurve.FullLevel.SemistableCovering q M' P W`](def/ModularCurve_FullLevelSemistableCovering.html#L28) — a family of Igusa component fields $F^{\mathrm{Ig}}_\ell$ indexed by $\ell \in$ [`CuspidalType.ProjLine q`](def/CuspidalType_IsCuspidalOfType.html#L21), supersingular component fields $F^{\mathrm{SS}}_s$ indexed by $s \in W$, component charts for each, annuli $\mathrm{An}$ and $\mathrm{An}'$ joining them, attaching places and the axioms of that structure — subject to the following clauses, each taken verbatim from its definition and summarised here: `𝒞.EquivClauses` (for each $\zeta$ and each $\gamma \in \Gamma_0(M')$ a permutation $\sigma$ of `ProjLine q` such that pullback along `levelAutBar q M' ζ γ` carries the $\ell$-th Igusa chart to the $\sigma(\ell)$-th in integers and domain, preserves each supersingular chart, and matches annuli domains and moduli); a per-point Drinfeld census clause, namely for every $\zeta$ and every $s \in W$ there is $\eta$ with $\eta = 1$ or $\eta = q$ such that `𝒞.DrinfeldClause π ι η ζ s` holds (existence of a subgroup $C$ of the $(q+1)$-st roots of unity of $\mathbb{F}_{q^2}$ and an isomorphism of $F^{\mathrm{SS}}_s$ with [`DrinfeldCurve.quotField q (ResidueField P) C`](def/ModularCurve_FullLevelSemistableCoveringW2.html#L32) over $\kappa(P)$ transporting the chart-induced actions of `levelAutBar q M' ζ γ⁻¹` for $\gamma \in \Gamma_0(M')$, and of the coefficientwise inertia automorphisms with $\iota(\alpha)$ equal to the tame character, into the explicit `hFunctionFieldAction` of the corresponding elements of `hSubgroup q`, the inertia half with exponent $\eta$ in $(\,$`diagOneElem q (d ^ η)⁻¹`$, \alpha^\eta)$); `𝒞.IgusaUnipotentClause ζ` for every $\zeta$ (for $\gamma \in \Gamma_0(M')$ with unipotent reduction mod $q$, the semilinear automorphism attached to `levelAutBar q M' ζ γ⁻¹` induces the identity on the Igusa chart at `lineInfty q`); `𝒞.LevelPinClauses hle R₀` (the two clauses pinning $R_0$ to the charts: for $s \in W$ and $f \in R_0.\mathrm{integers}$ regular wherever $j_q$ is, if the $R_0$-residue of $f$ lies in the valuation subring of $s$ then the image of $f$ in `fieldBar q M'` is a chart integer at $s$ with residue the image of the evaluation of that residue at $s$; and for each $\ell$ a ring homomorphism $j$ from `modularFunctionFieldC (ResidueField P) M'` to $F^{\mathrm{Ig}}_\ell$ compatible with residues of $R_0$ and matching the valuation subring of $s$ with that of $\mathcal{C}.\mathrm{xs}\,\ell\,s$); `𝒞.InertiaClause π` (for $\tau$ in inertia with tame character $1$ the coefficientwise automorphism induces the identity on every Igusa and supersingular chart, preserves their place maps and domains, and preserves the domains and both parameters of every annulus); `𝒞.WidthClause ⟨π, hπP⟩` (every annulus modulus is a unit of $P$ times $\pi^w$ with $w \geq 1$); `𝒞.GenusClause` (the genus of `fieldBar q M'` over $\overline{\mathbb{Q}}$ plus $\#\mathbb{P}^1(\mathbb{F}_q) + |W|$ equals the sum of the genera of the Igusa and supersingular components plus $\#\mathbb{P}^1(\mathbb{F}_q)\cdot|W| + 1$); `𝒞.DiscFibreClause` (all Igusa and supersingular charts have discrete fibres); `𝒞.CurveClause` (each $F^{\mathrm{Ig}}_\ell$ and $F^{\mathrm{SS}}_s$ is a curve over $\kappa(P)$ and essentially of finite type over it); and `𝒞.NaturalityClauses` (four compatibilities: for $\tau$ in inertia the supersingular charts are preserved with induced $\kappa(P)$-algebra automorphism compatible with place maps; the same for `levelAutBar q M' ζ γ⁻¹` with $\gamma \in \Gamma_0(M')$; for $\gamma$ with unipotent reduction the Igusa chart at infinity is preserved with identity induced map; and there is $\zeta_0$ such that pullback along `levelAutBar q M' ζ₀ γ⁻¹` carries the $\ell$-th Igusa chart, and the attached annuli domains, to those at $(\mathrm{red}_q\gamma)^{-1}\cdot\ell$).
--
--   Next, a $\mathbb{Q}_\lambda$-linear reduction map $\mathrm{red}$ from $V_{\mathrm{inv}}$ to the product over the telescope indices $i$ of the rational Tate modules of $\mathrm{Pic}^0(\kappa(P), \mathcal{C}.\mathrm{teleFbar}\,i)$ is given, subject to four hypotheses. The chartwise law: for $v \in V_{\mathrm{inv}}$ and $x \in T_\lambda \mathrm{Pic}^0(\overline{\mathbb{Q}},$`fieldBar q M'`$)$ with $v = 1 \otimes x$, for every level $k$, every degree-zero divisor $D$ whose class is the $k$-th projection of $x$, and every decomposition $D = \sum_i D_i$ with each $D_i$ supported in the domain of the chart $\mathcal{C}.\mathrm{teleChart}\,i$ and of degree zero, for each $i$ there is $y \in T_\lambda \mathrm{Pic}^0(\kappa(P), \mathcal{C}.\mathrm{teleFbar}\,i)$ with $\mathrm{red}\,v\,i = 1 \otimes y$ and such that for every degree-zero divisor $E$ equal to the pushforward of $D_i$ along the chart's place map, the $k$-th projection of $y$ is the class of $E$. The kernel law: for $v \in V_{\mathrm{inv}}$, $\mathrm{red}\,v = 0$ if and only if $v$ lies in the $\mathbb{Q}_\lambda$-span of the elements $s\,w - w$ with $s \in S$ and $w$ arbitrary in the rational Tate module. The existence of chart-supported representatives: for $v \in V_{\mathrm{inv}}$, $x$ with $v = 1 \otimes x$, and every $k$, there exist a degree-zero divisor $D$ whose class is the $k$-th projection of $x$ and a decomposition $D = \sum_i D_i$ with each $D_i$ supported in the domain of $\mathcal{C}.\mathrm{teleChart}\,i$ and of degree zero. And rationality: every place in the domain of every chart $\mathcal{C}.\mathrm{teleChart}\,i$ is rational, i.e. $\overline{\mathbb{Q}}$ maps onto its residue field.
--
--   A span law of Picard–Lefschetz type is assumed on the rational Tate module of `Jac q M'`: for every $\tau$ in `P.inertiaSubgroupIn ℚ` with `P.tameCharacter π τ = 1`, the range of the base change of `tateGal q M' lam τ` minus the identity is contained in the $\mathbb{Q}_\lambda$-span of those $x$ for which there exist $g \in \mathrm{GL}_2(\mathbb{Z}/q)$ and a vector $v$ fixed by the base-changed action of every unipotent [`CuspidalType.unipotent q t`](def/CuspidalType_IsCuspidalOfType.html#L27), $t \in \mathbb{Z}/q$, with $x$ the image of $v$ under the base-changed action of $g$.
--
--   Finally, coordinates and projectors are given. A $\mathbb{Z}_\lambda$-linear isomorphism $\Psi$ from $T_\lambda($`Jac q M'`$)$ to the functions from `Idx q` to $T_\lambda($`jacComp q M'`$)$ is assumed to satisfy four laws: it is coordinatewise evaluation at each level $n$; it is Galois equivariant in the twisted sense $\Psi(\tau_\sigma x)(\zeta) =$ `JH.tateGaloisRep (q ^ 2 * M') (levelH q M') lam σ` applied to $\Psi x (\sigma^{-1}\cdot\zeta)$; it transports the action of `slJac q M' γ` for $\gamma \in \mathrm{SL}_2(\mathbb{Z})$ into `JH.tateEnd` of `levelOp q M' ζ γ⁻¹`; and it transports the action of `diagJac q M' d` into reindexing by $\zeta \mapsto \zeta^{d^{-1}}$ via `Idx.pow`. A $\mathbb{Q}_\lambda$-linear endomorphism $e_{\mathcal{C}}$ of the rational Tate module of `Jac q M'` is assumed to fix every vector $v$ satisfying the cuspidality condition that $\sum_{t \in \mathbb{Z}/q} \rho(u(t))\rho(g)\,v = 0$ for all $g \in \mathrm{GL}_2(\mathbb{Z}/q)$, where $\rho$ is the base-changed action `tateGL2 q M' lam`. A $\mathbb{Q}_\lambda$-linear map $e_{\mathrm{inv}}$ from the rational Tate module of `jacComp q M'` to $V_{\mathrm{inv}}$ is assumed to restrict to the identity on $V_{\mathrm{inv}}$, and for every $v$ and every $\zeta$ the $\zeta$-coordinate `ratCoord q M' lam Ψ ζ (eC v)` is assumed to lie in $V_{\mathrm{inv}}$. Lastly, for each $\zeta$ and each $s \in W$ a $\mathbb{Q}_\lambda$-linear map $\Phi\,\zeta\,s$ from the rational Tate module of $\mathrm{Pic}^0(\kappa(P), \mathcal{C}.\mathrm{teleFbar}(\mathcal{C}.\mathrm{eSS}\,s))$ to that of $\mathrm{Pic}^0(\kappa(P),$[`DrinfeldCurve.drinfeldFunctionField q (ResidueField P)`](def/DrinfeldCurve_FunctionField.html#L12)$)$ is given, and all these maps are assumed injective.
--
--   Under all of the above, the conclusion is: for every $v$ in the rational Tate module of `Jac q M'` such that $\sum_{t \in \mathbb{Z}/q} \rho(u(t))\rho(g)\,v = 0$ for every $g \in \mathrm{GL}_2(\mathbb{Z}/q)$, and such that [`ModularCurve.FullLevel.cuspidalSpecialization q M' lam (ResidueField P) Ψ eC Vinv eInv red 𝒞.eSS Φ v = 0`](def/ModularCurve_FullLevelCuspidalSpecialization.html#L49) — that is, $v$ is killed by the composite of $e_{\mathcal{C}}$ with the component specialisation assembled from $\Psi$, $e_{\mathrm{inv}}$, $\mathrm{red}$ and $\Phi$, with values in [`DrinfeldCurve.tateProd q (ResidueField P) lam ℚ_[lam] (Idx q × ↥W)`](def/DrinfeldCurve_TateRep.html#L27) — one has $v = 0$.
--
--   This is the injectivity half of the cuspidal specialisation law at full level $q$, in the case $q = 3$, where the Drinfeld census is supplied chart by chart with an inertia exponent $\eta \in \{1, q\}$ hedged per supersingular point rather than uniformly. It says that a vector of the rational $\lambda$-adic Tate module of the full-level Jacobian which is cuspidal, in the sense of being annihilated by all the operators $\sum_{t}\rho(u(t))\rho(g)$, is detected by its reductions along the Igusa and supersingular components of a semistable covering at a place above $q$; it feeds the construction of the specialisation map used in the analysis of the mod $q$ Galois representation at full level $q$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_eq_zero_of_cuspidalSpecialization_eq_zero_of_forall_sum_unipotent_eq_zero_of_semistableCovering_of_reduction_of_eq_three.lean

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

theorem ModularCurve.FullLevel.eq_zero_of_cuspidalSpecialization_eq_zero_of_forall_sum_unipotent_eq_zero_of_semistableCovering_of_reduction_of_eq_three
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
