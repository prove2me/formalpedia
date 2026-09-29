-- Prove2me | Theorems.Thm_ModularCurve_XHDRModelAtP_exists_forall_exists_mem_riemannRochSpace_sub_and_residue_eq_of_hasValue_leading_of_nonneg_of_annulus_offDiag_of_wgen
-- name    : ModularCurve.XHDRModelAtP.exists_forall_exists_mem_riemannRochSpace_sub_and_residue_eq_of_hasValue_leading_of_nonneg_of_annulus_offDiag_of_wgen
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.68297+00:00
-- url     : https://prove2.me/theorems/31112fc9-21d6-5b90-8dfc-c01a76f65cf3
-- title:
--   Lifting node-compatible fibre pairs to L(D₀-E) across a supersingular annulus
-- statement:
--   Setting. Fix a prime $p$ and $M$ with $p \mid M$ but $p^2 \nmid M$, a subgroup $H \le (\mathbb{Z}/M)^\times$ containing every unit whose image under `ZMod.unitsMap` for $M/p \mid M$ is trivial, and the hypothesis that the $q$-expansion $j$-invariant `jqModC ℚ` lies in the full-level $q$-expansion function field; let $\mathfrak{X}$ be a term of `XHDRModelAtP p M H hpM hj`, the bundled integral model of $X_H(M)$ at $p$ together with its generic curve model `𝔛.Meta` over $\overline{\mathbb{Q}}$ with function field $F_M =$ `xHFunctionFieldBar M H`, its isomorphism `𝔛.eeta` onto the base change of `toBase p (ΓM M H) hj` along $R_p \to \overline{\mathbb{Q}}$, and the remaining structure fields of `XHDRModelAtP`.
--
--   Valuation-theoretic data. $A$ is a valuation subring of $\overline{\mathbb{Q}}$ with `A.LiesOverPrime p`, i.e. $p$ is a non-unit of $A$, whose residue field $\kappa =$ `ResidueField ↥A` is algebraically closed of characteristic $p$; $\rho : R_p \to A$ is a ring homomorphism whose composite with the inclusion $A \hookrightarrow \overline{\mathbb{Q}}$ is the structure map $R_p \to \overline{\mathbb{Q}}$ (hypothesis `hρ`). Write $\bar F =$ `JHNeronObjectAtP.Fbar p M H hpM κ` for the $q$-expansion function field of level `ΓN p M H hpM` over $\kappa$.
--
--   The diamond twist. $pb$ is a unit of $\mathbb{Z}/(M/p)$ whose underlying residue class is $p$ (hypothesis `hpb`), and $\delta$ is a self-map of the places of $\bar F$ over $\kappa$ which, by `hδ`, is the action of the semilinear automorphism attached to `diamondActionModL κ (M/p) (infSubgroup p M H hpM) (CuspForm.gammaLift (M/p) pb)`, where `infSubgroup p M H hpM` is the image of $H$ under reduction to $(\mathbb{Z}/(M/p))^\times$.
--
--   The node set. $SS$ is a finite set of pairs of places of $\bar F$ which, by `hSS`, is exactly `ssNodePairsQExp κ (ΓN p M H hpM) p`: the pairs $s$ with $s_2$ supersingular and $s_1 =$ `qExpFrobeniusPlaceModL` applied to $s_2$.
--
--   Correspondence data. $\theta$ is a $\overline{\mathbb{Q}}$-algebra automorphism of $F_M$, and $\alpha$ is a $\overline{\mathbb{Q}}$-algebra map from $F_{M/p} =$ `xHFunctionFieldBar (M/p) (infSubgroup p M H hpM)` to $F_M$, with $\alpha$ integral (`hα`) and $\theta \circ \alpha$ integral (`hβ`). Two compatibility hypotheses on $q$-expansions are imposed: `hα_coe`, that $\alpha$ is the identity on underlying Laurent series, and `hβ_coe`, that the Laurent series of $(\theta \circ \alpha)(u)$ is `qExpand` by $p$ of that of $u$. Hypothesis `hθgal` asserts that $\theta$ commutes with the arithmetic Galois action of every $\sigma \in \mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ on $F_M$.
--
--   Specialisation and prolongation data. $Psp$ is a term of `JHPlaceSpecialization p M H hpM A`, i.e. a specialisation map $\mathrm{sp}$ from places of $F_{M/p}$ to places of $\bar F$ together with a map on degree-zero divisor classes and the compatibilities recorded in that structure; `reduceFst` and `reduceSnd` denote $W \mapsto \mathrm{sp}(W|_\alpha)$ and $W \mapsto \delta(\mathrm{sp}(W|_{\theta\alpha}))$, restriction being along the given integral algebra maps. $Rpd$ is a `ProlongationDatum` for $Psp$ and $\theta$, consisting of two regular prolongations $R_1, R_2$ of $F_M$ with values in $\bar F$, linked by $f \in R_2$ iff $\theta f \in R_1$ and by the matching of residues.
--
--   Geometric hypotheses on $\mathfrak{X}$. `hwgen` states that for two $\overline{\mathbb{Q}}$-sections $y, y'$ of `𝔛.Meta.toBase`, if the composite of $y'$ with `𝔛.eeta`, the first pullback projection and the isomorphism `𝔛.w.hom` agrees with the composite of $y$ with `𝔛.eeta` and the first projection, then the place attached to $y'$ by `𝔛.Meta.pointEquivPlace` is the image of the place attached to $y$ under the semilinear automorphism of $\theta$. The two hypotheses `hcompat` and `hcompat'` describe, for $i \in \{0,1\}$, a section $y$ as above, a lift $u$ over `Spec.map (CommRingCat.ofHom ρ)`, a residue-field point $u\kappa$ of the fibre with the two stated compatibilities, and a closed point $P_0$ of the fibre curve model `𝔛.Mfib A hA ρ hρ` lying over the closed point of $u\kappa$: `hcompat` asserts that the place of $P_0$ equals `Psp.reduceFst` of the place of $y$ when $i = 0$ and `Psp.reduceSnd` of it when $i = 1$; `hcompat'` asserts, in the case $i = 0$, that `Psp.reduceSnd` of the place of $y$ equals $\delta$ applied to the mod-$p$ Frobenius place of the place of $P_0$, and in the case $i = 1$ that `Psp.reduceFst` of the place of $y$ equals the mod-$p$ Frobenius place of the place of $P_0$.
--
--   Laws of the datum. The hypotheses `hTD` (type dichotomy: every place $W$ of $F_M$ satisfies `reduceFst W` = Frobenius of `reduceSnd W`, or $\delta$ of Frobenius of `reduceFst W` = `reduceSnd W`), `hmodel` (the conjunction of the two divisor laws and the two cusp laws for $R_1, R_2$), `hO` (the order law at $\delta$-fixed affine places), `hRL` (the regularity law relative to $SS$) and `hNV` (the node value law relative to $SS$) are imposed, each for the pair $(\alpha, \theta \circ \alpha)$ and the twist $\delta$.
--
--   The annulus. $s \in SS$ is a node pair, $e_s$ a positive natural number, and $An$ an [`AlgebraicCurve.Annulus`](def/AlgebraicCurve_SemistableCharts.html#L86) for $A$ and $F_M$, with domain `An.dom`, parameter `An.param` and modulus `An.modulus` in the maximal ideal of $A$. Hypothesis `hdom` identifies `An.dom` as the set of places $W$ of $F_M$ with `reduceFst W` $= s_1$ and with neither `IsStrictFst` nor `IsStrictSnd` holding for $W$; `hmodulus` asserts `An.modulus` $= p^{e_s} u$ for some unit $u \in A$; `hinert` asserts that `An.param` is fixed by the arithmetic Galois action of every element of the inertia subgroup of $A$ over $\mathbb{Q}$. Hypothesis `hz₁` places $(\text{modulus})^{-1} \cdot \text{param}$ in the integers of $R_1$, and `hz₂` places `An.param` in the integers of $R_2$ with nonzero residue. Two attainment hypotheses are imposed: `hatt₂` says that the $R_2$-residue of `An.param` has order $1$ at $s_2$ and that for every $f$ in the integers of $R_2$ with nonzero residue and with $\mathrm{ord}_P f = 0$ for all $P \in$ `An.dom`, the value $P(f) \cdot P(\text{param})^{-\mathrm{ord}_{s_2}(\mathrm{res}_2 f)}$ lies in $A$ and is a unit there, for every $P \in$ `An.dom`; `hatt₁` is the corresponding statement for $R_1$, $s_1$ and the element $\text{modulus} \cdot \text{param}^{-1}$, whose $R_1$-residue is required to have order $1$ at $s_1$.
--
--   The configuration. $E$ is a finitely supported function from the places of $F_M$ to $\mathbb{Z}$, supported inside `An.dom` (`hE`) and pointwise non-negative (`hE0`); $m$ is an integer and $u \in A$ a unit such that, in $\overline{\mathbb{Q}}$, $u \cdot (\text{modulus})^m = \prod_V (-V(\text{param}))^{E(V)}$ (hypothesis `hlead`), the product being `E.prod`.
--
--   Conclusion. There exists a natural number $N_0$ such that for every divisor $D_0$ of $F_M$ over $\overline{\mathbb{Q}}$ with $D_0 \ge 0$ and `Psp.IsGoodDiv` (every place in the support of $D_0$ is strict for the first or the second reduction), such that $N_0 \le \deg$ of the pushforward under `reduceFst` of `Psp.fstDiv D₀` and $N_0 \le \deg$ of the pushforward under `reduceSnd` of `Psp.sndDiv D₀`, the following holds for all $g_1, g_2 \in \bar F$: if
--
--   $g_1$ lies in the Riemann–Roch space of $(\text{reduceFst})_* (\text{fstDiv } D_0) - m\,[s_1]$, and $g_2$ lies in the Riemann–Roch space of $(\text{reduceSnd})_* (\text{sndDiv } D_0) - \big(\textstyle\sum_V E(V) - m\big)[s_2]$, and
--
--   for every $t \in SS$ with $t \ne s$ there is $c \in \kappa$ with $t_1$.HasValue $g_1\,c$ and $t_2$.HasValue $g_2\,c$, and
--
--   there is $\lambda \in \kappa$ such that $s_2$ takes the value $\lambda$ on $g_2 \cdot (\mathrm{res}_2(\text{param}))^{-(\sum_V E(V) - m)}$ and $s_1$ takes the value $(\text{residue of } u)\cdot\lambda$ on $g_1 \cdot (\mathrm{res}_1(\text{modulus}\cdot\text{param}^{-1}))^{-m}$,
--
--   then there exist $G \in F_M$, a witness that $G$ lies in the integers of $R_1$, a witness that $G$ lies in the integers of $R_2$, such that $G$ lies in the Riemann–Roch space of $D_0 - E$, the $R_1$-residue of $G$ is $g_1$, and the $R_2$-residue of $G$ is $g_2$.
--
--   This is the linear-algebra lifting step for the Deligne–Rapoport model of $X_H(M)$ at a prime exactly dividing the level: a pair of sections on the two components of the geometric special fibre that agree at all nodes except one, and that satisfy the prescribed leading-value relation at the remaining node $s$, is the pair of residues of a single function in $L(D_0 - E)$ integral for both Gauss prolongations. It is used in the deduction of the order relations for an effective configuration placed on a supersingular annulus.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XHDRModelAtP_exists_forall_exists_mem_riemannRochSpace_sub_and_residue_eq_of_hasValue_leading_of_nonneg_of_annulus_offDiag_of_wgen.lean

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_ModularCurve_JHPlaceSpecialization
import Definitions.Def_ModularCurve_ComponentGroup
import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_AlgebraicCurve_Repartitions

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian IsLocalRing ModularCurve ModularCurve.XHDRLevel ModularCurve.JZeroNeronObjectAtP
open AlgebraicCurve

open scoped MatrixGroups

theorem ModularCurve.XHDRModelAtP.exists_forall_exists_mem_riemannRochSpace_sub_and_residue_eq_of_hasValue_leading_of_nonneg_of_annulus_offDiag_of_wgen
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

    (hO : Rpd.OrderLawFixed α (θ.toAlgHom.comp α) hα hβ δ)
    (hRL : Rpd.RegularityLaw α (θ.toAlgHom.comp α) hα hβ δ SS) (hNV : Rpd.NodeValueLaw α (θ.toAlgHom.comp α) hα hβ δ SS)

    (hθgal : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (f : ↥(xHFunctionFieldBar M H)),
      θ (arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ • f) =
        arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ • θ f)

    (hβ_coe : ∀ u, (((θ.toAlgHom.comp α) u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = qExpand (AlgebraicClosure ℚ) p (u : LaurentSeries (AlgebraicClosure ℚ)))

    (s : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) ×
      Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))) (hs : s ∈ SS)
    (es : ℕ) (hes : 0 < es) (An : AlgebraicCurve.Annulus A ↥(xHFunctionFieldBar M H))
    (hdom : ∀ W : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H),
      W ∈ An.dom ↔ (Psp.reduceFst α hα W = s.1 ∧ ¬ Psp.IsStrictFst α (θ.toAlgHom.comp α) hα hβ δ W ∧ ¬ Psp.IsStrictSnd α (θ.toAlgHom.comp α) hα hβ δ W))
    (hmodulus : ∃ u : ↥A, IsUnit u ∧ An.modulus = ((p : ℕ) : ↥A) ^ es * u)
    (hinert : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, σ ∈ A.inertiaSubgroupIn ℚ →
      (arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ) • An.param = An.param)
    (hz₁ : algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) ((An.modulus : AlgebraicClosure ℚ))⁻¹ * An.param ∈ Rpd.R₁.integers)
    (hz₂ : ∃ h₂ : An.param ∈ Rpd.R₂.integers, Rpd.R₂.residue ⟨An.param, h₂⟩ ≠ 0)
    (hatt₂ : ∃ h₂ : An.param ∈ Rpd.R₂.integers, s.2.ord (Rpd.R₂.residue ⟨An.param, h₂⟩) = 1 ∧
      ∀ (f : ↥(xHFunctionFieldBar M H)) (hf : f ∈ Rpd.R₂.integers), Rpd.R₂.residue ⟨f, hf⟩ ≠ 0 →
        (∀ P ∈ An.dom, P.ord f = 0) → ∀ P ∈ An.dom,
          ∃ h : P.evalAt f * (P.evalAt An.param) ^ (-(s.2.ord (Rpd.R₂.residue ⟨f, hf⟩))) ∈ A, IsUnit (⟨_, h⟩ : ↥A))
    (hatt₁ : ∃ h₁ : algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) ((An.modulus : ↥A) : AlgebraicClosure ℚ) * An.param⁻¹ ∈ Rpd.R₁.integers,
      s.1.ord (Rpd.R₁.residue ⟨_, h₁⟩) = 1 ∧
      ∀ (f : ↥(xHFunctionFieldBar M H)) (hf : f ∈ Rpd.R₁.integers), Rpd.R₁.residue ⟨f, hf⟩ ≠ 0 →
        (∀ P ∈ An.dom, P.ord f = 0) → ∀ P ∈ An.dom,
          ∃ h : P.evalAt f * (P.evalAt (algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) ((An.modulus : ↥A) : AlgebraicClosure ℚ) * An.param⁻¹)) ^
            (-(s.1.ord (Rpd.R₁.residue ⟨f, hf⟩))) ∈ A, IsUnit (⟨_, h⟩ : ↥A))

    (E : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) →₀ ℤ) (hE : ∀ V, E V ≠ 0 → V ∈ An.dom)
    (hE0 : ∀ V, 0 ≤ E V)
    (m : ℤ) (u : ↥A) (hu : IsUnit u)
    (hlead : ((u : ↥A) : AlgebraicClosure ℚ) * ((An.modulus : ↥A) : AlgebraicClosure ℚ) ^ m
      = E.prod (fun V n => (-(V.evalAt An.param)) ^ n))
    :
    ∃ N₀ : ℕ, ∀ (D₀ : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)), 0 ≤ D₀ →
      Psp.IsGoodDiv α (θ.toAlgHom.comp α) hα hβ δ D₀ →
      (N₀ : ℤ) ≤ Divisor.degree (Finsupp.mapDomain (Psp.reduceFst α hα) (Psp.fstDiv α (θ.toAlgHom.comp α) hα hβ δ D₀)) →
      (N₀ : ℤ) ≤ Divisor.degree (Finsupp.mapDomain (Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ) (Psp.sndDiv α (θ.toAlgHom.comp α) hα hβ δ D₀)) →
      ∀ (g₁ g₂ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))),
        g₁ ∈ riemannRochSpace (Finsupp.mapDomain (Psp.reduceFst α hα) (Psp.fstDiv α (θ.toAlgHom.comp α) hα hβ δ D₀) - Finsupp.single s.1 m) →
        g₂ ∈ riemannRochSpace (Finsupp.mapDomain (Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ) (Psp.sndDiv α (θ.toAlgHom.comp α) hα hβ δ D₀) - Finsupp.single s.2 ((E.sum fun _ n => n) - m)) →

        (∀ t ∈ SS, t ≠ s → ∃ c : ResidueField ↥A, t.1.HasValue g₁ c ∧ t.2.HasValue g₂ c) →

        (∃ lam : ResidueField ↥A,
          s.2.HasValue (g₂ * (Rpd.R₂.residue ⟨An.param, hz₂.fst⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))) ^ (-((E.sum fun _ n => n) - m))) lam ∧
          s.1.HasValue (g₁ * (Rpd.R₁.residue ⟨_, hatt₁.fst⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))) ^ (-m)) (IsLocalRing.residue ↥A u * lam)) →
        ∃ (G : ↥(xHFunctionFieldBar M H)) (h₁ : G ∈ Rpd.R₁.integers) (h₂ : G ∈ Rpd.R₂.integers),
          G ∈ riemannRochSpace (D₀ - E) ∧ Rpd.R₁.residue ⟨G, h₁⟩ = g₁ ∧ Rpd.R₂.residue ⟨G, h₂⟩ = g₂ := by sorry
