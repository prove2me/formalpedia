-- Prove2me | Theorems.Thm_ModularCurve_XHDRModelAtP_isOpenImmersion_and_exists_functionField_ringEquiv_of_genericFibre
-- name    : ModularCurve.XHDRModelAtP.isOpenImmersion_and_exists_functionField_ringEquiv_of_genericFibre
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:47.08657+00:00
-- url     : https://prove2.me/theorems/8be9f530-4c97-5bce-96b4-56a6ec86ab7f
-- title:
--   Geometric generic fibre: open immersion and function field
-- statement:
--   Fix a prime $p$ and a nonzero $M$ with $p \mid M$, a subgroup $H \le (\mathbb{Z}/M)^\times$, and the hypothesis `hj` that the Laurent series `jqModC ℚ` lies in the intermediate field `qExpFunctionFieldC ℚ ⊤` of $\mathbb{Q}((q))$ generated over $\mathbb{Q}$ by the integral-form ratios for $\mathrm{SL}(2,\mathbb{Z})$. Let $\mathfrak{X}$ be a term of `XHDRModelAtP p M H hpM hj`; among its data are the structure morphism `toBase p (ΓM M H) hj` of the two-chart integral model over $R_p$, a curve model $\mathfrak{X}.\mathrm{Meta}$ over $\overline{\mathbb{Q}}$ whose function field is identified by `ffEquiv` with `xHFunctionFieldBar M H` (the base change to $\overline{\mathbb{Q}}$ of `xHFunctionField M H`), and an isomorphism $\mathfrak{X}.\mathrm{eeta}$ from $\mathfrak{X}.\mathrm{Meta}.C$ onto the base change of the model along $R_p \to \overline{\mathbb{Q}}$. Let $P \subseteq \overline{\mathbb{Q}}$ be a valuation subring with $p$ a nonunit of $P$, and $\rho \colon R_p \to P$ a ring homomorphism whose composite with the inclusion $P \hookrightarrow \overline{\mathbb{Q}}$ is the structure map; assume the pullback $\mathfrak{X}_P$ of `toBase` along $\operatorname{Spec}\rho$ is an integral scheme. Let $g_A \colon \mathfrak{X}.\mathrm{Meta}.C \to \mathfrak{X}_P$ satisfy $g_A$ followed by the first projection equals $\mathfrak{X}.\mathrm{eeta}$ followed by the first projection, and $g_A$ followed by the second projection equals $\mathfrak{X}.\mathrm{Meta}.\mathrm{toBase}$ followed by $\operatorname{Spec}$ of $P \hookrightarrow \overline{\mathbb{Q}}$. Then $g_A$ is an open immersion, and there is a ring isomorphism $e$ from the function field of $\mathfrak{X}_P$ onto `xHFunctionFieldBar M H` such that for every open $U \subseteq \mathfrak{X}_P$ with $g_A^{-1}U$ nonempty and every $a \in \Gamma(\mathfrak{X}_P, U)$, the image under $e$ of the germ of $a$ at the generic point equals $\mathfrak{X}.\mathrm{Meta}.\mathrm{ffEquiv}^{-1}$ applied to the germ at the generic point of $g_A^{*}a$ on $g_A^{-1}U$.
--
--   This is the statement that the geometric generic fibre of the Deligne–Rapoport integral model of $X_H(M)$ over a valuation subring of $\overline{\mathbb{Q}}$ above $p$ is an open immersion, together with the resulting compatible identification of the function field of the base-changed model with $\overline{\mathbb{Q}}\cdot F(\Gamma_H(M))$ realised inside Laurent series. It is used in the analysis of points and divisors on the model over such a place, in particular in the study of annuli on $\mathfrak{X}_P$ and in the comparison of Néron-model points with $q$-expansions.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XHDRModelAtP_isOpenImmersion_and_exists_functionField_ringEquiv_of_genericFibre.lean

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_ModularCurve_JHNeronObjectAtP

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian IsLocalRing AlgebraicCurve
  ModularCurve ModularCurve.XHDRLevel ModularCurve.JZeroNeronObjectAtP
open scoped MatrixGroups

theorem ModularCurve.XHDRModelAtP.isOpenImmersion_and_exists_functionField_ringEquiv_of_genericFibre
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)
    (Pl : ValuationSubring (AlgebraicClosure ℚ)) (hPl : Pl.LiesOverPrime p)
    (ρ : R p →+* ↥Pl) (hρ : Pl.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))
    [IsIntegral (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ)))]
    (gA : 𝔛.Meta.C ⟶ (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))))
    (hgA₁ : gA ≫ pullback.fst _ _ = 𝔛.eeta ≫ pullback.fst _ _)
    (hgA₂ : gA ≫ pullback.snd _ _ = 𝔛.Meta.toBase ≫ barPt Pl) :
    IsOpenImmersion gA ∧
    ∃ e : (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).functionField ≃+* ↥(xHFunctionFieldBar M H),
      ∀ (U : (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).Opens)
        (hne : Nonempty (Scheme.Opens.toScheme (gA ⁻¹ᵁ U))) (a : Γ((pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))), U)),
        haveI : Nonempty (Scheme.Opens.toScheme U) := by
          obtain ⟨⟨x, hx⟩⟩ := hne
          exact ⟨⟨gA.base x, hx⟩⟩
        e ((pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).germToFunctionField U a) =
          𝔛.Meta.ffEquiv.symm (𝔛.Meta.C.germToFunctionField (gA ⁻¹ᵁ U) ((gA.app U).hom a)) := by sorry
