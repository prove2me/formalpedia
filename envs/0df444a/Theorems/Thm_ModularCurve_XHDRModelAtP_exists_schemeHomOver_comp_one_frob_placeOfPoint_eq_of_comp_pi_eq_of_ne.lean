-- Prove2me | Theorems.Thm_ModularCurve_XHDRModelAtP_exists_schemeHomOver_comp_one_frob_placeOfPoint_eq_of_comp_pi_eq_of_ne
-- name    : ModularCurve.XHDRModelAtP.exists_schemeHomOver_comp_one_frob_placeOfPoint_eq_of_comp_pi_eq_of_ne
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:47.08657+00:00
-- url     : https://prove2.me/theorems/4ced4c6f-97f0-5824-bff4-5aa2da14f75c
-- title:
--   Unramifiedness of π and Frobenius on a second preimage
-- statement:
--   Fix a prime $p$ and $M$ with $p \mid M$ (and $M/p \neq 0$), a subgroup $H \le (\mathbb{Z}/M)^{\times}$, and the hypothesis $hj$ that $\mathrm{jqModC}\,\mathbb{Q}$ lies in the $q$-expansion function field of the full modular group; let $\mathfrak{X}$ be a term of `XHDRModelAtP p M H hpM hj`, a bundle of properness, flatness, normality, smoothness and special-fibre data for the two-chart integral model `X p (ΓM M H) hj` over $\operatorname{Spec}(R\,p)$ together with its forgetful map $\mathfrak{X}.\pi$ to the $\Gamma_N$-level model. Let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ with $p$ a nonunit of $A$, with algebraically closed residue field of characteristic $p$, and $\rho : R\,p \to A$ a ring map compatible with $R\,p \to \overline{\mathbb{Q}}$. Let $y$ be a section of $\mathfrak{X}.\mathrm{Meta}.\mathrm{toBase}$ over $\operatorname{Spec}\overline{\mathbb{Q}}$, i.e. a $\overline{\mathbb{Q}}$-point of the geometric generic fibre model, and $u$ a morphism $\operatorname{Spec}A \to X\,p\,(\Gamma_M M H)\,hj$ over $\operatorname{Spec}\rho$ whose base change along $A \hookrightarrow \overline{\mathbb{Q}}$ is $y$ transported through $\mathfrak{X}.\mathrm{eeta}$ and the first projection. Let $u_\kappa$ be a morphism from the spectrum of the residue field $\kappa$ of $A$ to the fibre of `toBase` over $\kappa$ which is a section of the second projection and whose first projection is the reduction of $u$; so $u_\kappa$ records the special point of $u$. Assume there is a closed point $P$ of $(\mathfrak{X}.\mathrm{Mfib}\,A\,hA\,\rho\,h\rho).C$ whose image under $\mathfrak{X}.\mathrm{efib}$ followed by the component map $\mathfrak{X}.\mathrm{comp}\ 0$ is the closed point of $u_\kappa$, and that the place $\mathrm{placeOfPoint}\,P$ is different from $\mathfrak{X}.\mathrm{placeOn0}\,n$ — the restriction of the place attached to the crossing $n$ along the mod-$p$ Frobenius map `qExpFrobeniusModL` — for every $n$ in the pullback of $\mathfrak{X}.\mathrm{comp}\ 0$ and $\mathfrak{X}.\mathrm{comp}\ 1$. Finally let $y'$ be a second $\overline{\mathbb{Q}}$-point with the same image as $y$ under $\mathfrak{X}.\pi$ (after $\mathfrak{X}.\mathrm{eeta}$ and the first projection) and $y' \neq y$. The conclusion is twofold: first, there is an open subscheme $V$ of $X\,p\,(\Gamma_M M H)\,hj$ containing the set-theoretic image of $u$ such that the inclusion of $V$ followed by $\mathfrak{X}.\pi$ is formally unramified; second, there is a morphism $u' : \operatorname{Spec}A \to X\,p\,(\Gamma_M M H)\,hj$ over $\operatorname{Spec}\rho$ whose base change to $\overline{\mathbb{Q}}$ is $y'$, with $u'$ followed by $\mathfrak{X}.\pi$ equal to $u$ followed by $\mathfrak{X}.\pi$, with image contained in $\mathfrak{X}.\mathrm{smoothLocus}$, and admitting a special point $u_\kappa'$ (a section of the second projection whose first projection is the reduction of $u'$) whose closed point lies outside the image of $\mathfrak{X}.\mathrm{comp}\ 0$ and equals the image of some closed point $P'$ under $\mathfrak{X}.\mathrm{efib}$ followed by $\mathfrak{X}.\mathrm{comp}\ 1$, with $\mathrm{qExpFrobeniusPlaceModL}\ \kappa\ (\Gamma_N p M H hpM)\ p$ applied to $\mathrm{placeOfPoint}\,P'$ equal to $\mathrm{placeOfPoint}\,P$.
--
--   This is the section-level form of the Deligne–Rapoport description of the degeneration of the level-$M$ modular curve at a prime $p \mid M$: the forgetful map to level $M/p$ is an isomorphism on one component of the geometric special fibre and purely inseparable (Frobenius) on the other, so a generic point reducing onto the first component away from the crossings has all its other preimages reducing onto the second component, at the Frobenius preimage of its place. It supports the later computations of pullbacks of divisors and of sections along $\pi$ on the generic fibre.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XHDRModelAtP_exists_schemeHomOver_comp_one_frob_placeOfPoint_eq_of_comp_pi_eq_of_ne.lean

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra AlgebraicCurve IsLocalRing
  ModularCurve ModularCurve.XHDRLevel
open scoped MatrixGroups

theorem ModularCurve.XHDRModelAtP.exists_schemeHomOver_comp_one_frob_placeOfPoint_eq_of_comp_pi_eq_of_ne
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) [NeZero (M / p)]
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))

    (y : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _})
    (u : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj))
    (hu : Spec.map (CommRingCat.ofHom A.subtype) ≫ u.1 = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _)
    (uκ : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))
    (huκ₁ : uκ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ u.1)
    (huκ₂ : uκ ≫ pullback.snd _ _ = 𝟙 _)
    (P : closedPoints (𝔛.Mfib A hA ρ hρ).C)
    (hP : (𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 0).base P.1 = uκ.base (IsLocalRing.closedPoint (ResidueField ↥A)))
    (hP₀ : ∀ n : ↥(pullback (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1)),
      (𝔛.Mfib A hA ρ hρ).placeOfPoint P ≠ 𝔛.placeOn0 A hA ρ hρ n)

    (y' : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _})
    (hπ : y'.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ ≫ 𝔛.π.1 = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ ≫ 𝔛.π.1)
    (hne : y' ≠ y) :

    (∃ V : (X p (ΓM M H) hj).Opens, Set.range u.1.base ⊆ (V : Set (X p (ΓM M H) hj)) ∧
      FormallyUnramified (V.ι ≫ 𝔛.π.1)) ∧
    ∃ u' : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj),
      Spec.map (CommRingCat.ofHom A.subtype) ≫ u'.1 = y'.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ ∧
      u'.1 ≫ 𝔛.π.1 = u.1 ≫ 𝔛.π.1 ∧
      Set.range u'.1.base ⊆ (𝔛.smoothLocus : Set (X p (ΓM M H) hj)) ∧
      ∃ uκ' : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ),
        uκ' ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ u'.1 ∧
        uκ' ≫ pullback.snd _ _ = 𝟙 _ ∧
        uκ'.base (IsLocalRing.closedPoint (ResidueField ↥A)) ∉ Set.range (𝔛.comp A hA ρ hρ 0).base ∧
        ∃ P' : closedPoints (𝔛.Mfib A hA ρ hρ).C,
          (𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 1).base P'.1 = uκ'.base (IsLocalRing.closedPoint (ResidueField ↥A)) ∧
          qExpFrobeniusPlaceModL (ResidueField ↥A) (ΓN p M H hpM) p ((𝔛.Mfib A hA ρ hρ).placeOfPoint P') =
            (𝔛.Mfib A hA ρ hρ).placeOfPoint P := by sorry
