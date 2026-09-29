-- Prove2me | Theorems.Thm_ModularCurve_exists_linearMap_injective_range_eq_dual_multiplicativeSubmodule_ssPolarDifferentials_of_jHNeronObjectAtP_of_twoCompRegularDifferentials_of_ordinary_torusCoords_of_mem_infSubgroup
-- name    : ModularCurve.exists_linearMap_injective_range_eq_dual_multiplicativeSubmodule_ssPolarDifferentials_of_jHNeronObjectAtP_of_twoCompRegularDifferentials_of_ordinary_torusCoords_of_mem_infSubgroup
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.903374+00:00
-- url     : https://prove2.me/theorems/649763ff-964f-5e06-8944-9a0451076d62
-- title:
--   Dual of P⁰ embeds in supersingular-polar differentials
-- statement:
--   Fix an odd prime $p$ and an integer $M \ge 1$ with $p \mid M$ but $p^2 \nmid M$, and a subgroup $H \le (\mathbb{Z}/M)^\times$ containing the kernel of the reduction $(\mathbb{Z}/M)^\times \to (\mathbb{Z}/(M/p))^\times$ (hypothesis `hHp`), together with a set $S$ of primes and the hypothesis `hin`, asserting [`ModularCurve.HeckeDiamondInputsHAll M H`](def/ModularCurve_XHOperators.html#L113): for every prime $\ell$ the Hecke inputs `HeckeInputsHAlong` over $\overline{\mathbb{Q}}$ for $(M,H,\ell)$ hold, and every $d \in (\mathbb{Z}/M)^\times$ is realised by an $\overline{\mathbb{Q}}$-algebra automorphism $\sigma$ of the function field $\overline{\mathbb{Q}}\cdot F_H(M)$ satisfying `IsDiamondAutHBar M H d σ`.
--
--   Hecke data. A commutative ring $\mathbb{T}$ which is a $\mathbb{Z}_p$-algebra acts on the Tate module $T_p J_H(M)$ — by definition the group of sequences $(x_n)_{n}$ in $J_H(M) = \mathrm{Pic}^0(\overline{\mathbb{Q}}, \overline{\mathbb{Q}}\cdot F_H(M))$ with $p^n x_n = 0$ and $p\,x_{n+1} = x_n$ — compatibly with the $\mathbb{Z}_p$-action; `hfaith` says the action is faithful. A map $op$ from the generators [`CohCarrier.Gen M S`](def/CohCarrier_Inst.html#L13) (the symbols $T_\ell$ for primes $\ell \notin S$ with $\ell \nmid M$, $U_q$ for primes $q \mid M$, and $\langle d\rangle$ for $d \in (\mathbb{Z}/M)^\times$) to $\mathbb{T}$ is required by `hop` to act on $T_p J_H(M)$ as the corresponding operator `tateGenOpH`, and by `hgen` to generate $\mathbb{T}$ as a $\mathbb{Z}_p$-algebra. An idempotent splitting $S'$ of $\mathbb{T}$ is given (a finite family of complete orthogonal idempotents $e_i$ together with maximal ideals $\mathfrak{m}_i$ exhausting the maximal spectrum and satisfying $e_i \in \mathfrak{m}_j \iff i \ne j$), with an index $i_0$ such that $op(U_p) \notin \mathfrak{m}_{i_0}$ (hypothesis `hord`, ordinarity).
--
--   The place and the module $P^0$. A valuation subring $Pl$ of $\overline{\mathbb{Q}}$ is given with $p$ in its set of nonunits (`hPl`), and its residue field is assumed algebraically closed of characteristic $p$. A $\mathbb{T}$-submodule $P0 \le T_p J_H(M)$ is given together with `hP0`, which characterises its elements as those $x$ lying in the corner submodule $e_{i_0}\,T_p J_H(M)$ on which the inertia subgroup of $Pl$ over $\mathbb{Q}$ acts through the cyclotomic character: $\rho(\sigma)x = \chi_{\mathrm{cyc},p}(\sigma)\,x$ for all $\sigma$ in that inertia subgroup.
--
--   Differentials. An algebraically closed field $K$ of characteristic $p$ (an $\mathbb{F}_p$-algebra) is given, and a ring homomorphism $\tau$ from $\mathbb{T}$ to the $K$-endomorphisms of the submodule $\mathrm{ssPolarDifferentials}$ of $\Omega^1$ of the $q$-expansion function field of $\Gamma_H(M/p)$ with $H' = \mathrm{infSubgroup}$, the image of $H$ in $(\mathbb{Z}/(M/p))^\times$, consisting of differentials polar only at the supersingular places. The hypothesis `h\tau` says $\tau(op(g))$ acts as `genDiffModL` for every generator $g$: by the definition of `genDiffModL`, $T_\ell$ and $U_q$ ($q \ne p$) act by the mod-$\ell$ Hecke operator on differentials, $U_p$ by the Frobenius-pushforward operator, and $\langle d\rangle$ by the diamond operator attached to the image of $d$.
--
--   Geometric and arithmetic input, all hypotheses summarised in blocks here. (i) The classical $j$-invariant $q$-series lies in the $q$-expansion function field of $SL(2,\mathbb{Z})$ (`hj`), and $\mathfrak{X}$ is a Deligne–Rapoport model `XHDRModelAtP p M H hpM hj`. (ii) An $\overline{\mathbb{Q}}$-algebra automorphism $\theta$ of $\overline{\mathbb{Q}}\cdot F_H(M)$ with `h\theta`: on Laurent series $\theta$ sends a function coming from level $(M/p,H')$ to its $q \mapsto q^p$ expansion; `hwgen` compares the place attached to a geometric point with the $\theta$-translate of the place of a point related to it by the Atkin–Lehner involution $\mathfrak{X}.w$. (iii) A ring homomorphism $\rho$ from the base ring $R_p$ into $Pl$ compatible with $\overline{\mathbb{Q}}$ (`h\rho`), level data $\Lambda$ at $Pl$ for $(p,M,H)$ with $\Lambda.\sigma_A$ induced by $\rho$ (`h\sigma A`), and a Néron object $O$ of `JHNeronObjectAtP p M H hpM Pl hPl \Lambda`. (iv) Representability hypotheses: `hD`, `hDQ`, `hrep\Lambda` assert that the designations built from $(O.G,O.g,\text{unit section})$, its base change to $\mathbb{Q}$, and the analogous level-$(M/p)$ designation from $\Lambda$ represent the relative sub-Picard functor cut out by fibrewise-algebraically-trivial rigidified line bundles; `hsepQ`, $ajQ$, $kQ$, $\overline{aj}$, $\overline{\varepsilon}$, `hpoinc`, `haj\varepsilon`, `hajcl`, `hkQ₁`, `hkQ₂`, `hajbar`, `hajbar_over`, `h\varepsilon bar`, `h\varepsilon bar_aj` fix the separatedness, the Abel–Jacobi morphism over $\mathbb{Q}$, the comparison of generic fibres, and the normalisation of the Poincaré bundle and of the zero section. (v) Points dictionaries: `hpts_law` ($O.\mathrm{pts}$ is a group homomorphism for the relative group law), `hAJ` (the point attached to a degree-zero divisor $(x)-(s)$ is $x$ composed with $\overline{aj}$), $\alpha_H,\beta_H$ integral $\overline{\mathbb{Q}}$-algebra maps from level $(M/p,H')$ to level $(M,H)$ with $q$-expansion normalisations `h\alpha q`, `h\beta q`, and `hdeg0`, `hdeg1`, `hpull0`, `hpull1`, `hpull`, `hpull_mul` describing the degeneracy push-forwards $O.\mathrm{degPts}$, the pull-backs $\alpha_{\mathrm{pull}}$ and the morphisms $\mathrm{degPull}$ on divisor classes and their additivity. (vi) Special-fibre dictionaries: `hsp` and `hsp\Lambda` describe, for $i \in \{0,1\}$, the reduction at $Pl$ of the class of a divisor $(y_1)-(y_2)$ in terms of glued Picard data on the supersingular set $O.\mathrm{ssFinset}$, respectively of divisor classes on the special-fibre function field; `hdia0` describes the reduction of diamond operators as the semilinear automorphism `diamondActionModL`; `Meta₀`, `eeta₀`, `heeta₀iso`, `heeta₀`, $\overline{aj}_0$, `hMeta₀π`, `hMeta₀πw`, `hajbar₀_over`, `hAJ₀` supply the level-$(M/p)$ curve model with its comparison of places along $\alpha_H$ and $\beta_H$ and its Abel–Jacobi normalisation. (vii) Frobenius and diamond data on the special fibre: $F$, $F^{-1}$, $F^*$, $\delta$ with `hF` ($F$ is the mod-$p$ Frobenius push-forward on $\mathrm{Pic}^0$), `hFinv` ($F$ and $F^{-1}$ are mutually inverse), `hFstar` ($F^* = p\,F^{-1}$), $pb$ a unit reducing to $p$ (`hpb`), `h\delta` ($\delta$ is the diamond action of $pb$), and `hpullsp` computing the pair of classes attached to $\mathrm{degPull}\,i$. (viii) Toric data: an isomorphism $B$ of the character lattice of $O.\mathrm{ssFinset}$ with $\mathbb{Z}^{O.\mathrm{toricRank}}$ and `htorus_coords`, which matches torus points with node units through $B$; `hinertF` and `hinertT` state that for $\sigma$ in inertia and $x$ an $m$-torsion class, $\sigma x - x$ lies in $O.\mathrm{finPts}\,m$ (all $m>0$), respectively in $O.\mathrm{toricPts}\,m$ (for $m$ coprime to $p$). (ix) Two-cusp comparison: an Atkin–Lehner datum $W$ for $(M,p)$, a unit $e \in (\mathbb{Z}/M)^\times$ whose image times $p$ is $1$ in $\mathbb{Z}/(M/p)$ (`he`), and a $\kappa$-linear isomorphism $\Phi_1$ from $\kappa \otimes_{\mathbb{F}_p} \mathrm{IntTwoCuspForms}(M,H,p)$ onto the two-component regular differentials at level $(M/p,H')$, with `h\Phi_1inf` (its first component, followed by the inclusion, is an `IsInfReductionMap`) and `h\Phi_1W` (its second component realises the $q$-expansion of the $W$-twisted diamond translate). (x) Ordinarity of inertia on the corner submodule, `hordI`. (xi) Base-change comparison to $K$: a $K$-linear injection $\Phi_K$ from $K \otimes_\kappa \Omega^1$ over $\kappa$ to $\Omega^1$ over $K$ with `h\Phi K` (compatibility with $f\,dg$ under coefficient extension of Laurent series), `h\Phi Kss` (it carries the base change of the supersingular-polar submodule onto the one over $K$), and `h\Phi Kop` (it intertwines the operators `genDiffModL`). (xii) Existence hypotheses `hCk`, `hCK` of Frobenius-pushforward operators on differentials over $\kappa$ and over $K$, `h\rho k`, `h\rho K` of diamond pull-back actions of $\Gamma_0(M/p)$ over $\kappa$ and over $K$, and injectivity `h\Theta k`, `h\Theta K` of the $q$-expansion maps `diffQExp` in both cases. (xiii) Finally a unit $d \in (\mathbb{Z}/M)^\times$ whose image in $\mathbb{Z}/(M/p)$ equals $p$ (`hd`), with the image of $d$ or its negative lying in $H'$ (`hdH`).
--
--   Conclusion. Under all of the above there exists a $K$-linear map
--   $$\Psi : \mathrm{Hom}(P0, K) \longrightarrow \mathrm{ssPolarDifferentials}\,K\,\Gamma_H(M/p)\,p,$$
--   from the additive-homomorphism group of $P0$ into $K$, such that: $\Psi$ is injective; $\Psi$ is equivariant for the $\mathbb{T}$-action in the sense that for every $t \in \mathbb{T}$ and all additive maps $\varphi,\psi : P0 \to K$ with $\psi(x) = \varphi(t\cdot x)$ for all $x \in P0$, one has $\Psi(\psi) = \tau(t)(\Psi(\varphi))$; and the range of $\Psi$ equals the range of the endomorphism $\tau(e_{i_0})$.
--
--   This is the umbrella statement corresponding to Wiles' comparison, in the ordinary case with $p \parallel M$, between the $\mathbb{Z}_p$-dual of the multiplicative part $P^0$ of the $e_{i_0}$-component of $T_p J_H(M)$ and the space of differentials on the level-$(M/p)$ modular curve in characteristic $p$ with poles only at supersingular points, carrying the Hecke action across. It is used by the companion statement that formulates the same comparison directly in terms of the Tate module of $J_H(M)$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_linearMap_injective_range_eq_dual_multiplicativeSubmodule_ssPolarDifferentials_of_jHNeronObjectAtP_of_twoCompRegularDifferentials_of_ordinary_torusCoords_of_mem_infSubgroup.lean

import Mathlib
import Definitions.Def_ModularCurve_XHDifferentialsModL
import Definitions.Def_ModularCurve_XHOperators
import Definitions.Def_IharaLemma_IdempotentSplitting
import Definitions.Def_EllipticCurve_FrobeniusTrace
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_AlgebraicGeometry_RelativePic0DesignationBaseChange
import Definitions.Def_AlgebraicCurve_GluedPic0Functoriality
import Definitions.Def_AlgebraicGeometry_RelSubPicBaseChange
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivOfPoint

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct MatrixGroups
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian IsLocalRing AlgebraicCurve
  KaehlerDifferential AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve
  ModularCurve ModularCurve.XHDRLevel ModularCurve.JZeroNeronObjectAtP ModularCurve.JHNeronObjectAtP

set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem ModularCurve.exists_linearMap_injective_range_eq_dual_multiplicativeSubmodule_ssPolarDifferentials_of_jHNeronObjectAtP_of_twoCompRegularDifferentials_of_ordinary_torusCoords_of_mem_infSubgroup
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (M : ℕ) [NeZero M] (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (H : Subgroup (ZMod M)ˣ)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (S : Set ℕ) (hin : ModularCurve.HeckeDiamondInputsHAll M H)
    {𝕋 : Type} [CommRing 𝕋] [Algebra ℤ_[p] 𝕋] [Module 𝕋 (TateModule p (ModularCurve.JH M H))]
    [IsScalarTower ℤ_[p] 𝕋 (TateModule p (ModularCurve.JH M H))]
    (hfaith : ∀ t : 𝕋, (∀ x : TateModule p (ModularCurve.JH M H), t • x = 0) → t = 0)
    (op : CohCarrier.Gen M S → 𝕋)
    (hop : ∀ (g : CohCarrier.Gen M S) (x : TateModule p (ModularCurve.JH M H)),
      op g • x = ModularCurve.tateGenOpH M H S p g x)
    (hgen : Algebra.adjoin ℤ_[p] (Set.range op) = ⊤)
    (S' : IharaLemma.IdempotentSplitting 𝕋) (i₀ : Fin S'.n)
    (hord : op (CohCarrier.Gen.U p Fact.out hpM) ∉ S'.𝔪 i₀)
    (Pl : ValuationSubring (AlgebraicClosure ℚ)) (hPl : Pl.LiesOverPrime p)
    (P0 : Submodule 𝕋 (TateModule p (ModularCurve.JH M H)))
    (hP0 : ∀ x : TateModule p (ModularCurve.JH M H), x ∈ P0 ↔
      x ∈ IharaLemma.cornerSubmodule (M := TateModule p (ModularCurve.JH M H)) (S'.e i₀) ∧
        ∀ σ ∈ Pl.inertiaSubgroupIn ℚ, ModularCurve.JH.tateGaloisRep M H p σ x =
          ((cyclotomicCharacter (AlgebraicClosure ℚ) p σ.toRingEquiv : ℤ_[p]ˣ) : ℤ_[p]) • x)
    (K : Type*) [Field K] [IsAlgClosed K] [Algebra (ZMod p) K]
    (τ : 𝕋 →+* Module.End K
      (ModularCurve.ssPolarDifferentials K
        (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) p))
    (hτ : ∀ (g : CohCarrier.Gen M S)
      (ω : ModularCurve.ssPolarDifferentials K
        (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) p),
      ((τ (op g) ω : ModularCurve.ssPolarDifferentials K
          (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) p) :
        Ω[ModularCurve.qExpFunctionFieldC K
            (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))⁄K]) =
        ModularCurve.genDiffModL K p M H hpM S g ω)

    [CharP (ResidueField ↥Pl) p] [IsAlgClosed (ResidueField ↥Pl)] [Algebra (ZMod p) (ResidueField ↥Pl)] [NeZero (M / p)]
    (hj : ModularCurve.jqModC ℚ ∈ ModularCurve.qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : ModularCurve.XHDRModelAtP p M H hpM hj)

    (θ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hθ : haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
      ∀ (f : ↥(xHFunctionFieldBar M H)) (u : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))), (f : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)) →
        ((θ f : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = qExpand (AlgebraicClosure ℚ) p (u : LaurentSeries (AlgebraicClosure ℚ)))
    (hwgen : ∀ (y y' : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _}),
      y'.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ ≫ 𝔛.w.hom = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ →
      𝔛.Meta.pointEquivPlace y' = SemilinearAut.ofAlgAut θ • 𝔛.Meta.pointEquivPlace y)
    (ρ : R p →+* ↥Pl) (hρ : Pl.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))
    (Λ : JHNeronObjectAtP.LevelData p M H hpM Pl) (O : JHNeronObjectAtP p M H hpM Pl hPl Λ)

    (hD : RepresentsRelSubPic (toBase p (ΓM M H) hj) 𝔛.εinf (algEquivZeroCut (toBase p (ΓM M H) hj) 𝔛.εinf) (⟨O.G, O.g, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).2⟩ : RelativePic0Designation (R p) (toBase p (ΓM M H) hj)))

    (hDQ : RepresentsRelSubPic (baseChange (R p) (toBase p (ΓM M H) hj) ℚ) (sectionBaseChange ℚ 𝔛.εinf)
        (algEquivZeroCut (baseChange (R p) (toBase p (ΓM M H) hj) ℚ) (sectionBaseChange ℚ 𝔛.εinf)) (((⟨O.G, O.g, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).2⟩ : RelativePic0Designation (R p) (toBase p (ΓM M H) hj))).baseChange ℚ))
    (hsepQ : IsSeparated (baseChange (R p) (toBase p (ΓM M H) hj) ℚ))
    (ajQ : SchemeHomOver (baseChange (R p) (toBase p (ΓM M H) hj) ℚ) (((⟨O.G, O.g, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).2⟩ : RelativePic0Designation (R p) (toBase p (ΓM M H) hj))).baseChange ℚ).toBase)
    (kQ : pullback (toBase p (ΓM M H) hj) (genPt p) ⟶ pullback (toBase p (ΓM M H) hj) (specMap (R p) ℚ))
    (ajbar : 𝔛.Meta.C ⟶ O.G)
    (εbar : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _})

    (αH βH : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hαint : αH.toRingHom.IsIntegral) (hβint : βH.toRingHom.IsIntegral)
    [HasPrincipalDivisors (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)]
    (αpull : Fin 2 → (JH (M / p) (infSubgroup p M H hpM) →+ JH M H))
    (degPull : Fin 2 → SchemeHomOver Λ.f O.g)

    (Meta₀ : CurveModel (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)))
    (eeta₀ : Meta₀.C ⟶ pullback (toBase p (XHDRLevel.ΓN p M H hpM) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ)))))
    (heeta₀iso : IsIso eeta₀)
    (ajbar₀ : Meta₀.C ⟶ Λ.X)

    (F Finv Fstar : Pic0 (ResidueField ↥Pl) (Fbar p M H hpM (ResidueField ↥Pl)) →+
        Pic0 (ResidueField ↥Pl) (Fbar p M H hpM (ResidueField ↥Pl)))
    (pb : (ZMod (M / p))ˣ)
    (δ : Pic0 (ResidueField ↥Pl) (Fbar p M H hpM (ResidueField ↥Pl)) →+
        Pic0 (ResidueField ↥Pl) (Fbar p M H hpM (ResidueField ↥Pl)))

    (B : characterLattice ↥O.ssFinset ≃+ (Fin O.toricRank → ℤ))

    (hσA : Λ.σA = Spec.map (CommRingCat.ofHom ρ))

    (hrepΛ : Nonempty (RepresentsRelSubPic (toBase p (XHDRLevel.ΓN p M H hpM) hj) (schemeHomOverComp 𝔛.εinf 𝔛.π)
          (algEquivZeroCut (toBase p (XHDRLevel.ΓN p M H hpM) hj) (schemeHomOverComp 𝔛.εinf 𝔛.π)) (⟨Λ.X, Λ.f, (Λ.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1, (Λ.L.one (𝟙 (Spec (CommRingCat.of (R p))))).2⟩ : RelativePic0Designation (R p) (toBase p (XHDRLevel.ΓN p M H hpM) hj))))

    (hpoinc : Nonempty (hDQ.poincare.L ≅ (BaseChange.ofR (toBase p (ΓM M H) hj) 𝔛.εinf ℚ
        (hD.poincare.pullbackAlong ⟨pullback.fst O.g (specMap (R p) ℚ), pullback.condition⟩)).L))

    (hajε : (sectionBaseChange ℚ 𝔛.εinf).1 ≫ ajQ.1 = (((⟨O.G, O.g, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).2⟩ : RelativePic0Designation (R p) (toBase p (ΓM M H) hj))).baseChange ℚ).zeroSection)

    (hajcl : (∀ (K : Type) [Field K] (t : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of ℚ))
          (x : SchemeHomOver t (baseChange (R p) (toBase p (ΓM M H) hj) ℚ)),
        Nonempty ((hDQ.poincare.pullbackAlong
            ⟨x.1 ≫ ajQ.1, (Category.assoc _ _ _).trans ((congrArg (x.1 ≫ ·) ajQ.2).trans x.2)⟩).L ≅
          (RelEffCartierDiv.ofPoint (baseChange (R p) (toBase p (ΓM M H) hj) ℚ) x.1 x.2).lineBundle ⊗
            (RelEffCartierDiv.ofPoint (baseChange (R p) (toBase p (ΓM M H) hj) ℚ) (t ≫ (sectionBaseChange ℚ 𝔛.εinf).1)
              ((Category.assoc _ _ _).trans ((congrArg (t ≫ ·) (sectionBaseChange ℚ 𝔛.εinf).2).trans
                (Category.comp_id t)))).idealModule)))

    (hkQ₁ : kQ ≫ pullback.fst (toBase p (ΓM M H) hj) (specMap (R p) ℚ) = pullback.fst (toBase p (ΓM M H) hj) (genPt p))
    (hkQ₂ : kQ ≫ pullback.snd (toBase p (ΓM M H) hj) (specMap (R p) ℚ) = pullback.snd (toBase p (ΓM M H) hj) (genPt p) ≫ specMap ℚ (AlgebraicClosure ℚ))

    (hajbar : ajbar = 𝔛.eeta ≫ kQ ≫ ajQ.1 ≫ pullback.fst O.g (specMap (R p) ℚ))
    (hajbar_over : ajbar ≫ O.g = 𝔛.Meta.toBase ≫ genPt p)
    (hεbar : εbar.1 ≫ 𝔛.eeta ≫ pullback.fst (toBase p (ΓM M H) hj) (genPt p) = genPt p ≫ 𝔛.εinf.1)
    (hεbar_aj : εbar.1 ≫ ajbar = genPt p ≫ (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1)

    (hpts_law : (∀ x y : JH M H,
        O.pts (x + y) = (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hD).mul _ (O.pts x) (O.pts y)))

    (hAJ : (∀ (x s : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _}),
        s.1 ≫ 𝔛.eeta ≫ pullback.fst (toBase p (ΓM M H) hj) (genPt p) = genPt p ≫ 𝔛.εinf.1 →
        ∃ Dv : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar M H)),
          (Dv : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) =
            Finsupp.single (𝔛.Meta.pointEquivPlace x) 1 - Finsupp.single (𝔛.Meta.pointEquivPlace s) 1 ∧
          (O.pts (Pic0.mk Dv)).1 = x.1 ≫ ajbar))

    (hαq : (∀ u : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)), ((αH u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ))))
    (hβq : (haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
        ∀ u : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)), ((βH u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = qExpand (AlgebraicClosure ℚ) p (u : LaurentSeries (AlgebraicClosure ℚ))))

    (hdeg0 : (∀ (Dv : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar M H))) (Dw : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)))),
        (Dw : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) = Divisor.pushforwardAlong αH hαint (Dv : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) →
        O.degPts 0 (Pic0.mk Dv) = Pic0.mk Dw))
    (hdeg1 : (∀ (Dv : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar M H))) (Dw : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)))),
        (Dw : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) = Divisor.pushforwardAlong βH hβint (Dv : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) →
        O.degPts 1 (Pic0.mk Dv) = Pic0.mk Dw))

    (hpull0 : (∀ (Dw : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)))) (Dv : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar M H))),
        (Dv : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) = Divisor.pullbackAlong αH hαint (Dw : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) →
        αpull 0 (Pic0.mk Dw) = Pic0.mk Dv))
    (hpull1 : (∀ (Dw : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)))) (Dv : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar M H))),
        (Dv : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) = Divisor.pullbackAlong βH hβint (Dw : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) →
        αpull 1 (Pic0.mk Dw) = Pic0.mk Dv))

    (hpull : (∀ (i : Fin 2) (x : JH (M / p) (infSubgroup p M H hpM)),
        (O.pts (αpull i x)).1 = (Λ.pts x).1 ≫ (degPull i).1))

    (hpull_mul : ∀ (i : Fin 2) {T : Scheme.{0}} (s : T ⟶ base p) (x y : SchemeHomOver s Λ.f),
      schemeHomOverComp (Λ.L.mul s x y) (degPull i) =
        O.L.mul s (schemeHomOverComp x (degPull i)) (schemeHomOverComp y (degPull i)))

    (hsp : (∀ (i : Fin 2)
      (y₁ : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _})
      (u₁ : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj))
      (_ : barPt Pl ≫ u₁.1 = y₁.1 ≫ 𝔛.eeta ≫ pullback.fst _ _)
      (_ : Set.range u₁.1.base ⊆ (𝔛.smoothLocus : Set (X p (ΓM M H) hj)))
      (uκ₁ : Spec (CommRingCat.of (ResidueField ↥Pl)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥Pl).comp ρ))
      (_ : uκ₁ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥Pl)) ≫ u₁.1)
      (_ : uκ₁ ≫ pullback.snd _ _ = 𝟙 _)
      (P₁ : closedPoints (𝔛.Mfib Pl hPl ρ hρ).C)
      (_ : (𝔛.efib Pl hPl ρ hρ ≫ 𝔛.comp Pl hPl ρ hρ i).base P₁.1 = uκ₁.base (IsLocalRing.closedPoint (ResidueField ↥Pl)))
      (y₂ : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _})
      (u₂ : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj))
      (_ : barPt Pl ≫ u₂.1 = y₂.1 ≫ 𝔛.eeta ≫ pullback.fst _ _)
      (_ : Set.range u₂.1.base ⊆ (𝔛.smoothLocus : Set (X p (ΓM M H) hj)))
      (uκ₂ : Spec (CommRingCat.of (ResidueField ↥Pl)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥Pl).comp ρ))
      (_ : uκ₂ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥Pl)) ≫ u₂.1)
      (_ : uκ₂ ≫ pullback.snd _ _ = 𝟙 _)
      (P₂ : closedPoints (𝔛.Mfib Pl hPl ρ hρ).C)
      (_ : (𝔛.efib Pl hPl ρ hρ ≫ 𝔛.comp Pl hPl ρ hρ i).base P₂.1 = uκ₂.base (IsLocalRing.closedPoint (ResidueField ↥Pl)))
      (Dv : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar M H)))
      (_ : (Dv : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) =
        Finsupp.single (𝔛.Meta.pointEquivPlace y₁) 1 - Finsupp.single (𝔛.Meta.pointEquivPlace y₂) 1)
      (x : ↥(GluingData.admissible O.ssFinset))
      (_ : (x : GluingData (ResidueField ↥Pl) (Fbar p M H hpM (ResidueField ↥Pl)) O.ssFinset).1 =
        (if i = 0 then Finsupp.single ((𝔛.Mfib Pl hPl ρ hρ).placeOfPoint P₁) 1 -
          Finsupp.single ((𝔛.Mfib Pl hPl ρ hρ).placeOfPoint P₂) 1 else 0))
      (_ : (x : GluingData (ResidueField ↥Pl) (Fbar p M H hpM (ResidueField ↥Pl)) O.ssFinset).2.1 =
        (if i = 1 then Finsupp.single ((𝔛.Mfib Pl hPl ρ hρ).placeOfPoint P₁) 1 -
          Finsupp.single ((𝔛.Mfib Pl hPl ρ hρ).placeOfPoint P₂) 1 else 0))
      (_ : (x : GluingData (ResidueField ↥Pl) (Fbar p M H hpM (ResidueField ↥Pl)) O.ssFinset).2.2 = 0),
      ∃ s : SchemeHomOver Λ.σA O.g,
        (O.pts (Pic0.mk Dv)).1 = barPt Pl ≫ s.1 ∧
        O.ptsSp.symm (schemeHomOverComp ⟨resPt Pl, rfl⟩ s) = GluedPic0.mk O.ssFinset x))

    (hspΛ : (∀ (i : Fin 2)
      (y₁ : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _})
      (u₁ : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj))
      (_ : barPt Pl ≫ u₁.1 = y₁.1 ≫ 𝔛.eeta ≫ pullback.fst _ _)
      (uκ₁ : Spec (CommRingCat.of (ResidueField ↥Pl)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥Pl).comp ρ))
      (_ : uκ₁ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥Pl)) ≫ u₁.1)
      (_ : uκ₁ ≫ pullback.snd _ _ = 𝟙 _)
      (Q₁ : closedPoints (𝔛.Mfib Pl hPl ρ hρ).C)
      (_ : (𝔛.efib Pl hPl ρ hρ).base Q₁.1 =
        (uκ₁ ≫ fibreMap (if i = 0 then 𝔛.π else 𝔛.πw) ((IsLocalRing.residue ↥Pl).comp ρ)).base
          (IsLocalRing.closedPoint (ResidueField ↥Pl)))
      (y₂ : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _})
      (u₂ : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj))
      (_ : barPt Pl ≫ u₂.1 = y₂.1 ≫ 𝔛.eeta ≫ pullback.fst _ _)
      (uκ₂ : Spec (CommRingCat.of (ResidueField ↥Pl)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥Pl).comp ρ))
      (_ : uκ₂ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥Pl)) ≫ u₂.1)
      (_ : uκ₂ ≫ pullback.snd _ _ = 𝟙 _)
      (Q₂ : closedPoints (𝔛.Mfib Pl hPl ρ hρ).C)
      (_ : (𝔛.efib Pl hPl ρ hρ).base Q₂.1 =
        (uκ₂ ≫ fibreMap (if i = 0 then 𝔛.π else 𝔛.πw) ((IsLocalRing.residue ↥Pl).comp ρ)).base
          (IsLocalRing.closedPoint (ResidueField ↥Pl)))
      (Dv : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar M H)))
      (_ : (Dv : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) =
        Finsupp.single (𝔛.Meta.pointEquivPlace y₁) 1 - Finsupp.single (𝔛.Meta.pointEquivPlace y₂) 1)
      (Dw : Divisor.degZero (K := ResidueField ↥Pl) (F := Fbar p M H hpM (ResidueField ↥Pl)))
      (_ : (Dw : Divisor (ResidueField ↥Pl) (Fbar p M H hpM (ResidueField ↥Pl))) =
        Finsupp.single ((𝔛.Mfib Pl hPl ρ hρ).placeOfPoint Q₁) 1 -
          Finsupp.single ((𝔛.Mfib Pl hPl ρ hρ).placeOfPoint Q₂) 1),
      ∃ s₀ : SchemeHomOver Λ.σA Λ.f,
        (Λ.pts (O.degPts i (Pic0.mk Dv))).1 = barPt Pl ≫ s₀.1 ∧
        Λ.ptsSp.symm (schemeHomOverComp ⟨resPt Pl, rfl⟩ s₀) = Pic0.mk Dw))

    (hdia0 : (∀ (e : (ZMod (M / p))ˣ) (P : closedPoints (𝔛.Mfib Pl hPl ρ hρ).C),
      ∃ h : (inv (𝔛.efib Pl hPl ρ hρ)).base
          ((fibreMap (overOfIso (𝔛.dia0 e) (𝔛.dia0_over e)) ((IsLocalRing.residue ↥Pl).comp ρ)).base
            ((𝔛.efib Pl hPl ρ hρ).base P.1)) ∈ closedPoints (𝔛.Mfib Pl hPl ρ hρ).C,
        (𝔛.Mfib Pl hPl ρ hρ).placeOfPoint ⟨_, h⟩ =
          SemilinearAut.ofAlgAut (diamondActionModL (ResidueField ↥Pl) (M / p) (infSubgroup p M H hpM)
            (CuspForm.gammaLift (M / p) e)) • (𝔛.Mfib Pl hPl ρ hρ).placeOfPoint P))

    (hinertF : (∀ (m : ℕ), 0 < m → ∀ σ ∈ Pl.inertiaSubgroupIn ℚ,
        ∀ x ∈ Pic0.torsion (AlgebraicClosure ℚ) (xHFunctionFieldBar M H) m, σ • x - x ∈ O.finPts m))

    (heeta₀ : eeta₀ ≫ pullback.snd _ _ = Meta₀.toBase)
    (hMeta₀π : ∀ (y : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _}) (y₀ : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Meta₀.C // q ≫ Meta₀.toBase = 𝟙 _}),
        y₀.1 ≫ eeta₀ ≫ pullback.fst _ _ = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ ≫ 𝔛.π.1 →
        Meta₀.pointEquivPlace y₀ = Place.restrictAlong αH hαint (𝔛.Meta.pointEquivPlace y))
    (hMeta₀πw : ∀ (y : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _}) (y₀ : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Meta₀.C // q ≫ Meta₀.toBase = 𝟙 _}),
        y₀.1 ≫ eeta₀ ≫ pullback.fst _ _ = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ ≫ 𝔛.w.hom ≫ 𝔛.π.1 →
        Meta₀.pointEquivPlace y₀ = Place.restrictAlong βH hβint (𝔛.Meta.pointEquivPlace y))
    (hajbar₀_over : ajbar₀ ≫ Λ.f = Meta₀.toBase ≫ genPt p)
    (hAJ₀ : ∀ (x₀ s₀ : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Meta₀.C // q ≫ Meta₀.toBase = 𝟙 _}),
        s₀.1 ≫ eeta₀ ≫ pullback.fst _ _ = genPt p ≫ 𝔛.εinf.1 ≫ 𝔛.π.1 →
        ∃ Dv₀ : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))),
          (Dv₀ : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) =
            Finsupp.single (Meta₀.pointEquivPlace x₀) 1 - Finsupp.single (Meta₀.pointEquivPlace s₀) 1 ∧
          (Λ.pts (Pic0.mk Dv₀)).1 = x₀.1 ≫ ajbar₀)

    (hF : ∀ z, F z = qExpFrobeniusPushforwardModL (ResidueField ↥Pl) (JHNeronObjectAtP.ΓN p M H hpM) p z)
    (hFinv : F.comp Finv = AddMonoidHom.id _ ∧ Finv.comp F = AddMonoidHom.id _)
    (hFstar : ∀ z, Fstar z = (p : ℤ) • Finv z)
    (hpb : ((pb : (ZMod (M / p))ˣ) : ZMod (M / p)) = (p : ZMod (M / p)))
    (hδ : ∀ z, δ z = SemilinearAut.ofAlgAut (diamondActionModL (ResidueField ↥Pl) (M / p) (infSubgroup p M H hpM)
        (CuspForm.gammaLift (M / p) pb)) • z)
    (hpullsp : ∀ (i : Fin 2) (x : SchemeHomOver (resPt Pl ≫ Λ.σA) Λ.f),
        GluedPic0.toPic0Pair O.ssFinset (O.ptsSp.symm (schemeHomOverComp x (degPull i))) =
          if i = 0 then (Λ.ptsSp.symm x, Fstar (Λ.ptsSp.symm x))
          else (Fstar (Λ.ptsSp.symm x), δ (Λ.ptsSp.symm x)))

    (htorus_coords : ∀ (χ : torusCoord (ResidueField ↥Pl) O.toricRank →ₐ[ResidueField ↥Pl] ResidueField ↥Pl)
        (w : ↥O.ssFinset → Additive (ResidueField ↥Pl)ˣ),
      NeronModelInfra.schemeHomOverComp (torusPt (ResidueField ↥Pl) O.toricRank χ) O.torusFibre =
          toFibrePt (O.ptsSp (GluedPic0.nodeUnit O.ssFinset w)) ↔
        ∀ a : characterLattice ↥O.ssFinset,
          ((∏ s, Additive.toMul (w s) ^ (a : ↥O.ssFinset → ℤ) s : (ResidueField ↥Pl)ˣ) : ResidueField ↥Pl) =
            χ (AddMonoidAlgebra.single (B a) 1))

    (hinertT : ∀ (m : ℕ), m.Coprime p → ∀ σ ∈ Pl.inertiaSubgroupIn ℚ,
      ∀ x ∈ Pic0.torsion (AlgebraicClosure ℚ) (ModularCurve.xHFunctionFieldBar M H) m, σ • x - x ∈ O.toricPts m)

    (W : ModularForm.AtkinLehnerDatum M p)
    (e : (ZMod M)ˣ) (he : ((ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) e : (ZMod (M / p))ˣ) : ZMod (M / p)) * (p : ZMod (M / p)) = 1)
    (Φ₁ : ResidueField ↥Pl ⊗[ZMod p] CuspForm.IntTwoCuspForms M H p ≃ₗ[ResidueField ↥Pl]
        ↥(ModularCurve.twoCompRegularDifferentials (ResidueField ↥Pl) (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) p))
    (hΦ₁inf : ModularCurve.IsInfReductionMap (ResidueField ↥Pl) p M H hpM
        (LinearMap.fst (ResidueField ↥Pl) _ _ ∘ₗ (Submodule.subtype _) ∘ₗ Φ₁.toLinearMap))
    (hΦ₁W : ∀ (f : CuspForm (CohCarrier.GammaH M H) 2)
        (hf : f ∈ CuspForm.twoCuspIntegralSet M H 2 p (⊥ : Subring ℂ))
        (pfW : PowerSeries ℤ), ModularCurve.IsIntegralQExp (ModularForm.alSlash W 2 ⇑(CuspForm.diamondLinH 2 e f)) pfW →
          ModularCurve.diffQExp (ModularCurve.qExpFunctionFieldC (ResidueField ↥Pl) (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)))
              ((Φ₁ ((1 : ResidueField ↥Pl) ⊗ₜ[ZMod p] CuspForm.intTwoCuspReduce M H p
                ⟨f, CuspForm.twoCuspIntegralSet_subset_twoCuspLattice M H 2 p ⊥ hf⟩)).1.2) =
            ModularCurve.intSeriesC (ResidueField ↥Pl) pfW)

    (hordI : ∀ σ ∈ Pl.inertiaSubgroupIn ℚ, ∀ σ' ∈ Pl.inertiaSubgroupIn ℚ,
      ∀ x ∈ IharaLemma.cornerSubmodule (M := TateModule p (ModularCurve.JH M H)) (S'.e i₀),
        ModularCurve.JH.tateGaloisRep M H p σ' (ModularCurve.JH.tateGaloisRep M H p σ x - x) =
          ((cyclotomicCharacter (AlgebraicClosure ℚ) p σ'.toRingEquiv : ℤ_[p]ˣ) : ℤ_[p]) •
            (ModularCurve.JH.tateGaloisRep M H p σ x - x))

    [Algebra (ResidueField ↥Pl) K]
    (ΦK : K ⊗[ResidueField ↥Pl] Ω[↥(ModularCurve.qExpFunctionFieldC (ResidueField ↥Pl) (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)))⁄ResidueField ↥Pl] →ₗ[K]
        Ω[↥(ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)))⁄K])
    (hΦKinj : Function.Injective ΦK)
    (hΦK : ∀ (c : K) (f g : ↥(ModularCurve.qExpFunctionFieldC (ResidueField ↥Pl) (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))))
        (f' g' : ↥(ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)))),
        (f' : LaurentSeries K) = ModularCurve.coeffMap (algebraMap (ResidueField ↥Pl) K) (f : LaurentSeries (ResidueField ↥Pl)) →
        (g' : LaurentSeries K) = ModularCurve.coeffMap (algebraMap (ResidueField ↥Pl) K) (g : LaurentSeries (ResidueField ↥Pl)) →
        ΦK (c ⊗ₜ[ResidueField ↥Pl] (f • D (ResidueField ↥Pl) ↥(ModularCurve.qExpFunctionFieldC (ResidueField ↥Pl) (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))) g)) =
          c • (f' • D K ↥(ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))) g'))
    (hΦKss : Submodule.map ΦK ((ModularCurve.ssPolarDifferentials (ResidueField ↥Pl) (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) p).baseChange K) =
        ModularCurve.ssPolarDifferentials K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) p)
    (hΦKop : ∀ g : CohCarrier.Gen M S,
        (ModularCurve.genDiffModL K p M H hpM S g) ∘ₗ ΦK = ΦK ∘ₗ (ModularCurve.genDiffModL (ResidueField ↥Pl) p M H hpM S g).baseChange K)

    (hCk : ∃ C : Ω[↥(ModularCurve.qExpFunctionFieldC (ResidueField ↥Pl) (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)))⁄ResidueField ↥Pl] →ₗ[ResidueField ↥Pl]
        Ω[↥(ModularCurve.qExpFunctionFieldC (ResidueField ↥Pl) (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)))⁄ResidueField ↥Pl],
      haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩; ModularCurve.IsFrobPushDiff (ResidueField ↥Pl) (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) p C)
    (hCK : ∃ C : Ω[↥(ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)))⁄K] →ₗ[K] Ω[↥(ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)))⁄K],
      haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩; ModularCurve.IsFrobPushDiff K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) p C)
    (hρk : ∃ ρ : CongruenceSubgroup.Gamma0 (M / p) →*
        (↥(ModularCurve.qExpFunctionFieldC (ResidueField ↥Pl) (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))) ≃ₐ[ResidueField ↥Pl] ↥(ModularCurve.qExpFunctionFieldC (ResidueField ↥Pl) (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)))),
      ModularCurve.IsDiamondPullbackModL (ResidueField ↥Pl) (M / p) (ModularCurve.infSubgroup p M H hpM) ρ)
    (hρK : ∃ ρ : CongruenceSubgroup.Gamma0 (M / p) →*
        (↥(ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))) ≃ₐ[K] ↥(ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)))),
      ModularCurve.IsDiamondPullbackModL K (M / p) (ModularCurve.infSubgroup p M H hpM) ρ)
    (hΘk : Function.Injective (ModularCurve.diffQExp (ModularCurve.qExpFunctionFieldC (ResidueField ↥Pl) (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)))))
    (hΘK : Function.Injective (ModularCurve.diffQExp (ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)))))

    (d : (ZMod M)ˣ) (hd : ((ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) d : (ZMod (M / p))ˣ) : ZMod (M / p)) = (p : ZMod (M / p)))
    (hdH : ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) d ∈ ModularCurve.infSubgroup p M H hpM ∨
      -ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) d ∈ ModularCurve.infSubgroup p M H hpM)
    :
    ∃ Ψ : (↥P0 →+ K) →ₗ[K]
        ModularCurve.ssPolarDifferentials K
          (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) p,
      Function.Injective Ψ ∧
      (∀ (t : 𝕋) (φ ψ : ↥P0 →+ K), (∀ x : ↥P0, ψ x = φ (t • x)) → Ψ ψ = τ t (Ψ φ)) ∧
      LinearMap.range Ψ = LinearMap.range (τ (S'.e i₀)) := by sorry
