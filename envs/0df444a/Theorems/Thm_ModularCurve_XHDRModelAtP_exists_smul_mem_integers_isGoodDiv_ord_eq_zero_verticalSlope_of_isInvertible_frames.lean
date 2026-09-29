-- Prove2me | Theorems.Thm_ModularCurve_XHDRModelAtP_exists_smul_mem_integers_isGoodDiv_ord_eq_zero_verticalSlope_of_isInvertible_frames
-- name    : ModularCurve.XHDRModelAtP.exists_smul_mem_integers_isGoodDiv_ord_eq_zero_verticalSlope_of_isInvertible_frames
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:47.08657+00:00
-- url     : https://prove2.me/theorems/afae8ebc-d2a9-5b40-8649-35307f352d41
-- title:
--   Vertical-slope function from a framed invertible module
-- statement:
--   Arithmetic and model data. Fix a prime $p$ and a nonzero level $M$ with $p \mid M$ (`hpM`) and $p^{2} \nmid M$ (`hpM2`), and a subgroup $H \le (\mathbb{Z}/M)^{\times}$ such that every unit of $\mathbb{Z}/M$ whose image under `ZMod.unitsMap` in $(\mathbb{Z}/(M/p))^{\times}$ is $1$ lies in $H$ (`hHp`), with $M/p$ nonzero; `hj` asserts that the $q$-expansion `jqModC ℚ` of $j$ lies in `qExpFunctionFieldC ℚ ⊤`. Let $\mathfrak{X}$ (`𝔛`) be a Deligne–Rapoport model datum `XHDRModelAtP p M H hpM hj`. Among its components are: the curve model `𝔛.Meta` over $\overline{\mathbb{Q}}$ of $F_M :=$ `xHFunctionFieldBar M H`, the base change to $\overline{\mathbb{Q}}$ of the $q$-expansion function field of $X_H(M)$; the isomorphism `𝔛.eeta` of `𝔛.Meta.C` with the generic-fibre pullback of `toBase p (ΓM M H) hj`; the automorphism `𝔛.w`; and, for a place as below, the curve model `𝔛.Mfib A hA ρ hρ` of the fibre at $p$ together with the maps `𝔛.efib A hA ρ hρ` and `𝔛.comp A hA ρ hρ i` ($i \in \{0,1\}$) recording its two components, and the bijections `𝔛.nodeEquiv`, `𝔛.placeOn0`, `𝔛.placeOn1` attached to its crossings (`𝔛.placeOn1 n` is the supersingular place `𝔛.nodeEquiv n` and `𝔛.placeOn0 n` its image under `qExpFrobeniusPlaceModL`).
--
--   The place. Let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ with $p$ a nonunit of $A$ (`hA`), whose residue field $\kappa =$ `ResidueField ↥A` is of characteristic $p$ and algebraically closed, and let $\rho :$ `R p` $\to A$ be a ring homomorphism whose composite with the inclusion $A \hookrightarrow \overline{\mathbb{Q}}$ is the structure map `algebraMap (R p) (AlgebraicClosure ℚ)` (`hρ`). Write $F_b :=$ `JHNeronObjectAtP.Fbar p M H hpM κ`, the $q$-expansion function field of `ΓN p M H hpM` over $\kappa$, and $\Phi :=$ `qExpFrobeniusPlaceModL κ (ΓN p M H hpM) p` for the Frobenius operation on places of $F_b$.
--
--   The diamond operator and the nodes. Let `pb` be a unit of $\mathbb{Z}/(M/p)$ whose underlying residue is $p$ (`hpb`), and let $\delta$ be a self-map of the places of $F_b$ which, by `hδ`, is the action on places of the semilinear automorphism `SemilinearAut.ofAlgAut` of the diamond automorphism `diamondActionModL κ (M / p) (infSubgroup p M H hpM) (CuspForm.gammaLift (M / p) pb)`, where `infSubgroup p M H hpM` is the image of $H$ in $(\mathbb{Z}/(M/p))^{\times}$. Let `SS` be a finite set of pairs of places of $F_b$ which, by `hSS`, consists exactly of the pairs in `ssNodePairsQExp κ (ΓN p M H hpM) p`, that is, of the pairs $(v_1,v_2)$ with $v_2$ in `ssPlacesQExp κ (ΓN p M H hpM) p` and $v_1 = \Phi(v_2)$.
--
--   Correspondence and specialisation data. Let $\theta$ be an automorphism of $F_M$ over $\overline{\mathbb{Q}}$ and $\alpha$ an algebra homomorphism from $F_{M/p} :=$ `xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)` to $F_M$, with $\alpha$ integral (`hα`) and $\alpha$ followed by $\theta$ integral (`hβ`). Let `Psp` be a place-specialisation datum `JHPlaceSpecialization p M H hpM A`, with underlying map `Psp.sp` from places of $F_{M/p}$ to places of $F_b$, and let `Rpd` be a prolongation datum for `Psp` and $\theta$, consisting of two regular prolongations `Rpd.R₁`, `Rpd.R₂` of $A$ to $F_M$ with values in $F_b$ (each with its subring `integers` and residue map `residue`), compatible through $\theta$. For a place $W$ of $F_M$ write $\mathrm{red}_1(W) :=$ `Psp.reduceFst α hα W` $=$ `Psp.sp` of the restriction of $W$ along $\alpha$, and $\mathrm{red}_2(W) :=$ `Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ W` $= \delta($`Psp.sp` of the restriction of $W$ along $\alpha$ followed by $\theta)$. A place $v$ of $F_b$ is `Fixed` for $\delta$ when $\Phi(\delta(\Phi(v))) = v$; $W$ is `IsStrictFst` when $\delta(\Phi(\mathrm{red}_1 W)) = \mathrm{red}_2 W$ and $\mathrm{red}_1 W$ is not `Fixed`, and `IsStrictSnd` when $\mathrm{red}_1 W = \Phi(\mathrm{red}_2 W)$ and $\mathrm{red}_2 W$ is not `Fixed`.
--
--   Compatibility hypotheses. `hwgen`: for any two sections $y,y'$ of `𝔛.Meta.toBase` over $\overline{\mathbb{Q}}$, if $y'$ followed by `𝔛.eeta`, the first projection and `𝔛.w.hom` equals $y$ followed by `𝔛.eeta` and the first projection, then `𝔛.Meta.pointEquivPlace y'` is the image of `𝔛.Meta.pointEquivPlace y` under the action of `SemilinearAut.ofAlgAut θ`. `hα_coe`: $\alpha$ is the identity on underlying Laurent series, i.e. the Laurent series of $\alpha u$ equals that of $u$ for every $u$. `hTD`: the type dichotomy `Psp.TypeDichotomy`, namely for every place $W$ of $F_M$ either $\mathrm{red}_1 W = \Phi(\mathrm{red}_2 W)$ or $\delta(\Phi(\mathrm{red}_1 W)) = \mathrm{red}_2 W$. `hmodel`: `Rpd.IsModel α (θ.toAlgHom.comp α) hα hβ δ`, the conjunction of the four clauses `DivisorLawFst`, `DivisorLawSnd`, `CuspLawInfty`, `CuspLawZero`.
--
--   Two reduction compatibilities, `hcompat` and `hcompat'`, are stated for the same configuration: an index $i \in \{0,1\}$, a section $y$ of `𝔛.Meta.toBase`, a morphism $u$ over `Spec.map ρ` to the integral model whose composite with `barPt A` agrees with $y$ followed by `𝔛.eeta` and the first projection, a $\kappa$-point $u_\kappa$ of the fibre of `(IsLocalRing.residue ↥A).comp ρ` compatible with $u$ through the residue map and a section of the second projection, and a closed point $P_0$ of `(𝔛.Mfib A hA ρ hρ).C` whose image under `𝔛.efib` followed by `𝔛.comp … i` is the closed point image of $u_\kappa$. Under these, `hcompat` asserts that `(𝔛.Mfib A hA ρ hρ).placeOfPoint P₀` equals $\mathrm{red}_1$ of the place of $y$ if $i = 0$ and $\mathrm{red}_2$ of the place of $y$ if $i = 1$; `hcompat'` asserts that for $i = 0$ one has $\mathrm{red}_2$ of the place of $y$ equal to $\delta(\Phi($`placeOfPoint P₀`$))$, and for $i = 1$ that $\mathrm{red}_1$ of the place of $y$ equals $\Phi($`placeOfPoint P₀`$)$.
--
--   Annuli at the nodes. Let $e :$ `SS` $\to \mathbb{N}$ with $e(s) > 0$ (`he`), and let `An` assign to each $s \in$ `SS` an annulus [`AlgebraicCurve.Annulus A F_M`](def/AlgebraicCurve_SemistableCharts.html#L86) (a set `dom` of places of $F_M$, a parameter `param`, and a modulus in the maximal ideal of $A$, subject to the axioms of that structure). The hypothesis `hAn` requires, for each $s$, seven clauses: (i) a place $W$ lies in `(An s).dom` if and only if $\mathrm{red}_1 W = s_1$ and $W$ is neither `IsStrictFst` nor `IsStrictSnd`; (ii) `(An s).modulus` is $p^{e(s)}$ times a unit of $A$; (iii) `(An s).param` is fixed by `arithmeticGalois (xHFunctionField M H) σ` for every $\sigma$ in the inertia subgroup `A.inertiaSubgroupIn ℚ`; (iv) the product of the inverse of the modulus with `param` lies in `Rpd.R₁.integers`; (v) `param` lies in `Rpd.R₂.integers` with nonzero `Rpd.R₂` residue; (vi) that residue has $\mathrm{ord}$ equal to $1$ at $s_2$, and for every $f \in$ `Rpd.R₂.integers` with nonzero residue and with $\mathrm{ord}_P f = 0$ at all $P \in$ `(An s).dom`, the element $f(P) \cdot (\mathrm{param}(P))^{-\mathrm{ord}_{s_2}(\overline{f})}$ lies in $A$ and is a unit there, for every such $P$ (values taken by `Place.evalAt`); (vii) the mirror clause for $\mathrm{modulus} \cdot \mathrm{param}^{-1}$: it lies in `Rpd.R₁.integers`, its `Rpd.R₁` residue has $\mathrm{ord}$ equal to $1$ at $s_1$, and the same unit statement holds with `Rpd.R₁`, $s_1$ and $\mathrm{modulus}\cdot\mathrm{param}^{-1}$ in place of `Rpd.R₂`, $s_2$ and `param`. Finally $k$ is a natural number divisible by every $e(s)$ (`hk`).
--
--   Geometric comparison data. Let $X_A :=$ `pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))`, assumed integral. Let `gA` be a morphism from `𝔛.Meta.C` to $X_A$ compatible with the first projection through `𝔛.eeta` (`hgA₁`) and with the second projection through `𝔛.Meta.toBase` followed by `barPt A` (`hgA₂`); let `bc` be a morphism from the fibre of `(IsLocalRing.residue ↥A).comp ρ` to $X_A$ compatible with both projections (`hbc₁`, `hbc₂`). Let `eK` be a ring isomorphism from the function field of $X_A$ to $F_M$ which, by `heK`, carries the germ at the generic point of a section $a$ over an open $U$ to the image under `𝔛.Meta.ffEquiv.symm` of the germ of the pullback of $a$ along `gA` over `gA ⁻¹ᵁ U`.
--
--   The framing hypothesis `hTW` posits a module $\mathcal{L}$ on $X_A$ satisfying `Scheme.Modules.IsInvertible`, together with additive maps $\varphi_U : \Gamma(\mathcal{L},U) \to$ (function field of $X_A$), subject to: compatibility with restriction to nonempty smaller opens; semilinearity, $\varphi_U(a \cdot m) = a \cdot \varphi_U(m)$ with $a$ mapped into the function field; injectivity of $\varphi_U$ for nonempty $U$; and five further groups of clauses, in each of which the reading of a section $m$ is $g =$ `eK (φ U m)` and `Scheme.Modules.IsFrameOn m U` is required. (a) At the crossings: for each $s$ in `SS` and each point $n$ of the pullback of `𝔛.comp … 0` and `𝔛.comp … 1` with `𝔛.placeOn0 n` $= s_1$ and `𝔛.placeOn1 n` $= s_2$, there are an open $U$ containing the image of $n$ in $X_A$ under `bc`, a nonempty-opens witness, a section $m$ framing $\mathcal{L}$ on $U$ whose reading $g$ is nonzero, and a nonzero $a \in \overline{\mathbb{Q}}$ such that for all $P \in$ `(An s).dom` one has $\mathrm{ord}_P g = 0$ and $g(P)\, a\, (\mathrm{param}(P))^{-k/e(s)} \in A$ is a unit there. (b) At the `Fixed` non-node points of the first component: for each closed point $Q$ of `(𝔛.Mfib A hA ρ hρ).C` whose place is `Fixed` for $\delta$ and differs from $s_1$ for all $s \in$ `SS`, there are $U$ containing the image of $Q$ under `𝔛.efib` followed by `𝔛.comp … 0` and `bc`, and a framing section whose reading $g$ satisfies $\mathrm{ord}_V g = 0$ for every place $V$ of $F_M$ with $\mathrm{red}_1 V$ the place of $Q$, and for which some $c \in \overline{\mathbb{Q}}$ has $c \cdot g \in$ `Rpd.R₁.integers` with nonzero residue of $\mathrm{ord}$ zero at the place of $Q$. (c) The analogue for the second component: if $\Phi$ of the place of $Q$ is `Fixed` and differs from $s_1$ for all $s \in$ `SS`, there are $U$ containing the image of $Q$ under `𝔛.efib` followed by `𝔛.comp … 1` and `bc`, and a framing section whose reading $g$ satisfies $\mathrm{ord}_V g = 0$ for every $V$ with $\mathrm{red}_1 V = \Phi($place of $Q)$ and $\mathrm{red}_2 V =$ place of $Q$. (d) There is one affine open `Uaff` of $X_A$ containing all the crossing images of (a), all the images of (b) and all those of (c), and moreover a closed point $Q$ whose place differs from $s_1$ for all $s \in$ `SS`, an open $U$ and a framing section over $U$ whose reading $g$ admits $c \in \overline{\mathbb{Q}}$ with $c \cdot g \in$ `Rpd.R₁.integers` of nonzero residue, the relevant image point lying in both $U$ and `Uaff`. (e) Strictness of all readings: for every closed point $x$ of `𝔛.Meta.C`, every open $U$ containing `gA.base x` and every section $m$ framing $\mathcal{L}$ on $U$ with reading $g$, if $\mathrm{ord}$ at `𝔛.Meta.placeOfPoint x` of $g$ is nonzero then that place is `IsStrictFst` or `IsStrictSnd`.
--
--   Conclusion. There exist $f \in F_M$, a constant $c \in \overline{\mathbb{Q}}$ and a witness that $c \cdot f \in$ `Rpd.R₁.integers`, such that: $f \neq 0$; the residue `Rpd.R₁.residue ⟨c • f, hc⟩` is nonzero; every divisor $G$ on $F_M$ with $G(V) = \mathrm{ord}_V f$ for all places $V$ satisfies `Psp.IsGoodDiv α (θ.toAlgHom.comp α) hα hβ δ G`, that is, every place in the support of $G$ is `IsStrictFst` or `IsStrictSnd`; for every place $V$ of $F_M$ such that $\mathrm{red}_1 V$ is `Fixed` for $\delta$ and differs from $s_1$ for all $s \in$ `SS`, one has $\mathrm{ord}_V f = 0$; for every place $v$ of $F_b$ which is `Fixed` for $\delta$ and differs from $s_1$ for all $s \in$ `SS`, the $\mathrm{ord}$ at $v$ of the residue of $c \cdot f$ is $0$; and for every $s$ in `SS` there is a nonzero $a \in \overline{\mathbb{Q}}$ such that for every $P \in$ `(An s).dom` one has $\mathrm{ord}_P f = 0$ and $f(P)\, a\, (\mathrm{param}(P))^{-k/e(s)}$ lies in $A$ and is a unit there, the exponent being minus the natural-number quotient $k/e(s)$ and the values being those of `Place.evalAt`.
--
--   This is the vertical-slope step in the analysis of the specialisation of places on the Deligne–Rapoport model of $X_H(M)$ at $p$: it converts a hypothesised invertible module on the model over $A$, framed at the crossings of the fibre and at the $\delta$-fixed non-node points of both components, into a single rational function on $X_H(M)$ over $\overline{\mathbb{Q}}$ whose divisor is good, which is unramified away from the nodes and whose prescribed behaviour on the node annuli is governed by the exponents $k/e(s)$. It feeds the corresponding statement in which the annulus data are supplied under divisibility and off-diagonal assumptions.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XHDRModelAtP_exists_smul_mem_integers_isGoodDiv_ord_eq_zero_verticalSlope_of_isInvertible_frames.lean

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_ModularCurve_JHPlaceSpecialization
import Definitions.Def_ModularCurve_ComponentGroup
import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicCurve
  IsLocalRing ModularCurve ModularCurve.XHDRLevel ModularCurve.JZeroNeronObjectAtP
open scoped MatrixGroups

set_option maxHeartbeats 400000 in
set_option synthInstance.maxHeartbeats 200000 in

theorem ModularCurve.XHDRModelAtP.exists_smul_mem_integers_isGoodDiv_ord_eq_zero_verticalSlope_of_isInvertible_frames
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)

    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))

    (pb : (ZMod (M / p))ˣ) (hpb : ((pb : (ZMod (M / p))ˣ) : ZMod (M / p)) = (p : ZMod (M / p)))
    (δ : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) → Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))
    (hδ : ∀ v, δ v = SemilinearAut.ofAlgAut (diamondActionModL (ResidueField ↥A) (M / p) (infSubgroup p M H hpM) (CuspForm.gammaLift (M / p) pb)) • v)

    (SS : Finset (Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) ×
      Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))))
    (hSS : ∀ s, s ∈ SS ↔ s ∈ ssNodePairsQExp (ResidueField ↥A) (ΓN p M H hpM) p)

    (θ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (α : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hα : α.IsIntegral) (hβ : (θ.toAlgHom.comp α).IsIntegral)
    (Psp : JHPlaceSpecialization p M H hpM A) (Rpd : JHPlaceSpecialization.ProlongationDatum Psp θ)

    (hwgen : ∀ (y y' : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _}),
          y'.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ ≫ 𝔛.w.hom = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ →
          𝔛.Meta.pointEquivPlace y' = SemilinearAut.ofAlgAut θ • 𝔛.Meta.pointEquivPlace y)
    (hα_coe : ∀ u, ((α u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)))
    (hTD : Psp.TypeDichotomy α (θ.toAlgHom.comp α) hα hβ δ) (hmodel : Rpd.IsModel α (θ.toAlgHom.comp α) hα hβ δ)

    (hcompat : ∀ (i : Fin 2)
        (y : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _})
        (u : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj))
        (_ : barPt A ≫ u.1 = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _)
        (uκ : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))
        (_ : uκ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ u.1)
        (_ : uκ ≫ pullback.snd _ _ = 𝟙 _)
        (P0 : closedPoints (𝔛.Mfib A hA ρ hρ).C)
        (_ : (𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ i).base P0.1 = uκ.base (IsLocalRing.closedPoint (ResidueField ↥A))),
        (𝔛.Mfib A hA ρ hρ).placeOfPoint P0 =
          if i = 0 then Psp.reduceFst α hα (𝔛.Meta.pointEquivPlace y)
          else Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ (𝔛.Meta.pointEquivPlace y))
    (hcompat' : ∀ (i : Fin 2)
        (y : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _})
        (u : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj))
        (_ : barPt A ≫ u.1 = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _)
        (uκ : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))
        (_ : uκ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ u.1)
        (_ : uκ ≫ pullback.snd _ _ = 𝟙 _)
        (P0 : closedPoints (𝔛.Mfib A hA ρ hρ).C)
        (_ : (𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ i).base P0.1 = uκ.base (IsLocalRing.closedPoint (ResidueField ↥A))),
        if i = 0 then
          Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ (𝔛.Meta.pointEquivPlace y) =
            δ (qExpFrobeniusPlaceModL (ResidueField ↥A) (ΓN p M H hpM) p ((𝔛.Mfib A hA ρ hρ).placeOfPoint P0))
        else
          Psp.reduceFst α hα (𝔛.Meta.pointEquivPlace y) =
            qExpFrobeniusPlaceModL (ResidueField ↥A) (ΓN p M H hpM) p ((𝔛.Mfib A hA ρ hρ).placeOfPoint P0))
    (e : ↥SS → ℕ) (he : ∀ s, 0 < e s)
    (An : ↥SS → AlgebraicCurve.Annulus A ↥(xHFunctionFieldBar M H))
    (hAn : ∀ s : ↥SS, ((∀ W : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H),
            W ∈ (An s).dom ↔ (Psp.reduceFst α hα W = s.1.1 ∧ ¬ Psp.IsStrictFst α (θ.toAlgHom.comp α) hα hβ δ W ∧ ¬ Psp.IsStrictSnd α (θ.toAlgHom.comp α) hα hβ δ W)) ∧
          (∃ u : ↥A, IsUnit u ∧ (An s).modulus = ((p : ℕ) : ↥A) ^ (e s) * u) ∧
          (∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, σ ∈ A.inertiaSubgroupIn ℚ →
            (arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ) • (An s).param = (An s).param) ∧
          algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (((An s).modulus : AlgebraicClosure ℚ))⁻¹ * (An s).param ∈ Rpd.R₁.integers ∧
          (∃ h₂ : (An s).param ∈ Rpd.R₂.integers, Rpd.R₂.residue ⟨(An s).param, h₂⟩ ≠ 0) ∧

          (∃ h₂ : (An s).param ∈ Rpd.R₂.integers, s.1.2.ord (Rpd.R₂.residue ⟨(An s).param, h₂⟩) = 1 ∧
            ∀ (f : ↥(xHFunctionFieldBar M H)) (hf : f ∈ Rpd.R₂.integers), Rpd.R₂.residue ⟨f, hf⟩ ≠ 0 →
              (∀ P ∈ (An s).dom, P.ord f = 0) → ∀ P ∈ (An s).dom,
                ∃ h : P.evalAt f * (P.evalAt (An s).param) ^ (-(s.1.2.ord (Rpd.R₂.residue ⟨f, hf⟩))) ∈ A, IsUnit (⟨_, h⟩ : ↥A)) ∧
          (∃ h₁ : algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (((An s).modulus : ↥A) : AlgebraicClosure ℚ) * (An s).param⁻¹ ∈ Rpd.R₁.integers,
            s.1.1.ord (Rpd.R₁.residue ⟨_, h₁⟩) = 1 ∧
            ∀ (f : ↥(xHFunctionFieldBar M H)) (hf : f ∈ Rpd.R₁.integers), Rpd.R₁.residue ⟨f, hf⟩ ≠ 0 →
              (∀ P ∈ (An s).dom, P.ord f = 0) → ∀ P ∈ (An s).dom,
                ∃ h : P.evalAt f * (P.evalAt (algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (((An s).modulus : ↥A) : AlgebraicClosure ℚ) * (An s).param⁻¹)) ^
                  (-(s.1.1.ord (Rpd.R₁.residue ⟨f, hf⟩))) ∈ A, IsUnit (⟨_, h⟩ : ↥A))))
    (k : ℕ) (hk : ∀ s : ↥SS, e s ∣ k)

    (gA : 𝔛.Meta.C ⟶ (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))))
    (hgA₁ : gA ≫ pullback.fst _ _ = 𝔛.eeta ≫ pullback.fst _ _)
    (hgA₂ : gA ≫ pullback.snd _ _ = 𝔛.Meta.toBase ≫ barPt A)
    (bc : fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ) ⟶ (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))))
    (hbc₁ : bc ≫ pullback.fst _ _ = pullback.fst _ _)
    (hbc₂ : bc ≫ pullback.snd _ _ = pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)))

    [IsIntegral (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ)))]
    (eK : (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).functionField ≃+* ↥(xHFunctionFieldBar M H))
    (heK : ∀ (U : (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).Opens) [Nonempty (Scheme.Opens.toScheme (gA ⁻¹ᵁ U))] [Nonempty (Scheme.Opens.toScheme U)] (a : Γ(pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ)), U)),
      eK ((pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).germToFunctionField U a) = 𝔛.Meta.ffEquiv.symm (𝔛.Meta.C.germToFunctionField (gA ⁻¹ᵁ U) ((gA.app U).hom a)))

    (hTW : ∃ (𝓛 : (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).Modules) (_ : Scheme.Modules.IsInvertible 𝓛)
        (φ : ∀ U : (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).Opens, Γ(𝓛, U) →+ ((pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).functionField : Type)),

        (∀ (U V : (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).Opens) (h : V ≤ U), Nonempty V →
          ∀ m : Γ(𝓛, U), φ V (𝓛.presheaf.map (homOfLE h).op m) = φ U m) ∧
        (∀ (U : (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).Opens) [Nonempty U] (a : Γ(pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ)), U)) (m : Γ(𝓛, U)),
          φ U (a • m) = algebraMap Γ(pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ)), U) (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).functionField a * φ U m) ∧
        (∀ U : (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).Opens, Nonempty U → Function.Injective (φ U)) ∧

        (∀ (s : ↥SS) (n : ↥(pullback (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1)))
      (_ : 𝔛.placeOn0 A hA ρ hρ n = s.1.1) (_ : 𝔛.placeOn1 A hA ρ hρ n = s.1.2),
          ∃ (U : (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).Opens) (_ : bc.base ((pullback.fst (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1) ≫ 𝔛.comp A hA ρ hρ 0).base n) ∈ U) (_ : Nonempty (Scheme.Opens.toScheme U)) (m : Γ(𝓛, U))
            (g : ↥(xHFunctionFieldBar M H)) (_ : g = eK (φ U m)),
            Scheme.Modules.IsFrameOn m U ∧ g ≠ 0 ∧ (∃ a : AlgebraicClosure ℚ, a ≠ 0 ∧ ∀ P ∈ (An s).dom, P.ord (g) = 0 ∧
            ∃ h : P.evalAt (g) * a * (P.evalAt (An s).param) ^ (-((k / e s : ℕ) : ℤ)) ∈ A, IsUnit (⟨_, h⟩ : ↥A))) ∧

        (∀ (Q : closedPoints (𝔛.Mfib A hA ρ hρ).C),
          JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ ((𝔛.Mfib A hA ρ hρ).placeOfPoint Q) →
          (∀ s ∈ SS, (𝔛.Mfib A hA ρ hρ).placeOfPoint Q ≠ s.1) →
          ∃ (U : (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).Opens) (_ : bc.base ((𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 0).base Q.1) ∈ U) (_ : Nonempty (Scheme.Opens.toScheme U)) (m : Γ(𝓛, U))
            (g : ↥(xHFunctionFieldBar M H)) (_ : g = eK (φ U m)),
            Scheme.Modules.IsFrameOn m U ∧
            (∀ V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), Psp.reduceFst α hα V = (𝔛.Mfib A hA ρ hρ).placeOfPoint Q → V.ord g = 0) ∧
            (∃ (c : AlgebraicClosure ℚ) (hc : c • g ∈ Rpd.R₁.integers), Rpd.R₁.residue ⟨c • g, hc⟩ ≠ 0 ∧
              ((𝔛.Mfib A hA ρ hρ).placeOfPoint Q).ord (Rpd.R₁.residue ⟨c • g, hc⟩ : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) = 0)) ∧

        (∀ (Q : closedPoints (𝔛.Mfib A hA ρ hρ).C),
          JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ (qExpFrobeniusPlaceModL (ResidueField ↥A) (ΓN p M H hpM) p ((𝔛.Mfib A hA ρ hρ).placeOfPoint Q)) →
          (∀ s ∈ SS, qExpFrobeniusPlaceModL (ResidueField ↥A) (ΓN p M H hpM) p ((𝔛.Mfib A hA ρ hρ).placeOfPoint Q) ≠ s.1) →
          ∃ (U : (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).Opens) (_ : bc.base ((𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 1).base Q.1) ∈ U) (_ : Nonempty (Scheme.Opens.toScheme U)) (m : Γ(𝓛, U))
            (g : ↥(xHFunctionFieldBar M H)) (_ : g = eK (φ U m)),
            Scheme.Modules.IsFrameOn m U ∧
            (∀ V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), Psp.reduceFst α hα V = qExpFrobeniusPlaceModL (ResidueField ↥A) (ΓN p M H hpM) p ((𝔛.Mfib A hA ρ hρ).placeOfPoint Q) →
              Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ V = (𝔛.Mfib A hA ρ hρ).placeOfPoint Q → V.ord g = 0)) ∧

        (∃ Uaff : (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).Opens, IsAffineOpen Uaff ∧
          (∀ (s : ↥SS) (n : ↥(pullback (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1))) (_ : 𝔛.placeOn0 A hA ρ hρ n = s.1.1) (_ : 𝔛.placeOn1 A hA ρ hρ n = s.1.2), bc.base ((pullback.fst (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1) ≫ 𝔛.comp A hA ρ hρ 0).base n) ∈ Uaff) ∧
          (∀ (Q : closedPoints (𝔛.Mfib A hA ρ hρ).C),
            JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ ((𝔛.Mfib A hA ρ hρ).placeOfPoint Q) →
          (∀ s ∈ SS, (𝔛.Mfib A hA ρ hρ).placeOfPoint Q ≠ s.1) → bc.base ((𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 0).base Q.1) ∈ Uaff) ∧
          (∀ (Q : closedPoints (𝔛.Mfib A hA ρ hρ).C),
            JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ (qExpFrobeniusPlaceModL (ResidueField ↥A) (ΓN p M H hpM) p ((𝔛.Mfib A hA ρ hρ).placeOfPoint Q)) →
          (∀ s ∈ SS, qExpFrobeniusPlaceModL (ResidueField ↥A) (ΓN p M H hpM) p ((𝔛.Mfib A hA ρ hρ).placeOfPoint Q) ≠ s.1) → bc.base ((𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 1).base Q.1) ∈ Uaff) ∧
          (∃ (Q : closedPoints (𝔛.Mfib A hA ρ hρ).C) (U : (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).Opens) (_ : bc.base ((𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 0).base Q.1) ∈ U) (_ : bc.base ((𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 0).base Q.1) ∈ Uaff)
            (_ : Nonempty (Scheme.Opens.toScheme U)) (m : Γ(𝓛, U)) (g : ↥(xHFunctionFieldBar M H)) (_ : g = eK (φ U m)),
              (∀ s ∈ SS, (𝔛.Mfib A hA ρ hρ).placeOfPoint Q ≠ s.1) ∧ Scheme.Modules.IsFrameOn m U ∧
              ∃ (c : AlgebraicClosure ℚ) (hc : c • g ∈ Rpd.R₁.integers), Rpd.R₁.residue ⟨c • g, hc⟩ ≠ 0)) ∧

        (∀ (x : closedPoints 𝔛.Meta.C) (U : (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).Opens), gA.base x.1 ∈ U → ∀ (m : Γ(𝓛, U)) (g : ↥(xHFunctionFieldBar M H)), g = eK (φ U m) →
          Scheme.Modules.IsFrameOn m U → (𝔛.Meta.placeOfPoint x).ord g ≠ 0 →
          Psp.IsStrictFst α (θ.toAlgHom.comp α) hα hβ δ (𝔛.Meta.placeOfPoint x) ∨ Psp.IsStrictSnd α (θ.toAlgHom.comp α) hα hβ δ (𝔛.Meta.placeOfPoint x)))
    :
    ∃ (f : ↥(xHFunctionFieldBar M H)) (c : AlgebraicClosure ℚ) (hc : c • f ∈ Rpd.R₁.integers),
          f ≠ 0 ∧ Rpd.R₁.residue ⟨c • f, hc⟩ ≠ 0 ∧
          (∀ G : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), (∀ V, G V = V.ord f) → Psp.IsGoodDiv α (θ.toAlgHom.comp α) hα hβ δ G) ∧
          (∀ V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ (Psp.reduceFst α hα V) →
            (∀ s ∈ SS, Psp.reduceFst α hα V ≠ s.1) → V.ord f = 0) ∧
          (∀ v : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)), JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ v → (∀ s ∈ SS, v ≠ s.1) →
            v.ord (Rpd.R₁.residue ⟨c • f, hc⟩ : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) = 0) ∧
          (∀ s : ↥SS, ∃ a : AlgebraicClosure ℚ, a ≠ 0 ∧ ∀ P ∈ (An s).dom, P.ord f = 0 ∧
            ∃ h : P.evalAt f * a * (P.evalAt (An s).param) ^ (-((k / e s : ℕ) : ℤ)) ∈ A, IsUnit (⟨_, h⟩ : ↥A)) := by sorry
