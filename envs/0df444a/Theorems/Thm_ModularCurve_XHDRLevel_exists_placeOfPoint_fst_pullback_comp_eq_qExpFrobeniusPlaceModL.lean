-- Prove2me | Theorems.Thm_ModularCurve_XHDRLevel_exists_placeOfPoint_fst_pullback_comp_eq_qExpFrobeniusPlaceModL
-- name    : ModularCurve.XHDRLevel.exists_placeOfPoint_fst_pullback_comp_eq_qExpFrobeniusPlaceModL
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.68297+00:00
-- url     : https://prove2.me/theorems/a263d1f6-a110-5af6-90e0-d641382fb9cc
-- title:
--   Place at a crossing is the Frobenius translate
-- statement:
--   Let $p$ be a prime and $M$ a nonzero natural number with $p \mid M$ and $p^2 \nmid M$, let $H \le (\mathbb{Z}/M)^\times$ be a subgroup containing every unit whose image under `ZMod.unitsMap` for the divisibility $M/p \mid M$ is trivial, and assume `jqModC ℚ` lies in `qExpFunctionFieldC ℚ ⊤`. The remaining data are: a morphism $\pi$ from `X p (ΓM M H) hj` to `X p (ΓN p M H hpM) hj` commuting with the structure maps to $\operatorname{Spec}(\mathrm{R\,p})$, an `R p`-algebra map `iota0` between the finite-chart algebras which is the identity on the underlying Laurent series and satisfies `ιFin p (ΓM M H) hj ≫ π.1 = Spec.map (CommRingCat.ofHom iota0.toRingHom) ≫ ιFin p (ΓN p M H hpM) hj`; a self-isomorphism $w$ of `X p (ΓM M H) hj` over the base and an `R p`-algebra automorphism `theta` of the finite chart at level `ΓM M H` such that `theta ∘ iota0` realises the substitution `qExpand ℚ p` (that is, $q \mapsto q^p$) on Laurent series; a valuation subring $A \subseteq \overline{\mathbb{Q}}$ in which $p$ is a nonunit, whose residue field $\kappa$ is algebraically closed of characteristic $p$, and a ring map $\rho : \mathrm{R\,p} \to A$ inducing the structure map to $\overline{\mathbb{Q}}$; two closed immersions `comp 0`, `comp 1` of the $\kappa$-fibre at level `ΓN p M H hpM` into the $\kappa$-fibre at level `ΓM M H`, both over $\operatorname{Spec}\kappa$, with `comp 0 ≫ fibreMap π = 𝟙` and `comp 0 ≫ fibreMap (overOfIso w hw) = comp 1`; a curve model `Mfib` over $\kappa$ (a proper smooth integral relative curve together with a ring isomorphism of its function field with `qExpFunctionFieldC κ (ΓN p M H hpM)` and a bijection of its closed points with the places) and an isomorphism `efib` of `Mfib.C` with that $\kappa$-fibre over $\operatorname{Spec}\kappa$, pinned by the condition `Mfib_pin` that the Laurent expansion read off from `Mfib` of a finite-chart function is the coefficientwise reduction modulo the maximal ideal of any lift of its $q$-expansion to $A$; and the hypothesis `hfrob` that for every closed point $P$ of `Mfib.C` the image of $P$ under `efib ≫ comp 1 ≫ fibreMap π`, transported back through `inv efib`, is again a closed point, whose place is `qExpFrobeniusPlaceModL κ (ΓN p M H hpM) p` applied to the place of $P$, i.e. the restriction of that place along the $p$-power $q$-expansion endomorphism. Giving $\kappa$ the `R p`-algebra structure through the composite of $\rho$ with the residue map, assume further given charts `c₀` and `c` on the two fibres, from the spectra of $\kappa \otimes_{\mathrm{R\,p}}$ (finite-chart algebra) at levels `ΓN p M H hpM` and `ΓM M H` respectively, each compatible with both pullback projections in the expected way, with `c` intertwining `fibreMap (overOfIso w hw)` with $\operatorname{Spec}$ of $\mathrm{id} \otimes \mathrm{theta}$, and such that every point of `pullback (comp 0) (comp 1)` has its second-projection image in the range of `c₀` on points. The conclusion is that for every point $n$ of `pullback (comp 0) (comp 1)` whose second projection, read in `Mfib.C` through `inv efib`, is a closed point, the first projection of $n$, read in `Mfib.C` through `inv efib`, is also a closed point, and its place equals `qExpFrobeniusPlaceModL κ (ΓN p M H hpM) p` of the place of the second.
--
--   In the Deligne–Rapoport picture of the reduction at $p$ of the modular curve of level divisible by exactly $p$, the fibre is the union of two copies of the level-prime-to-$p$ curve, and this statement records that at a crossing of the two copies the place attached to the coordinate on the first copy is the $p$-power $q$-expansion Frobenius translate of the place attached to the coordinate on the second. It feeds the identification of the crossings with supersingular points used in the level-lowering step, and is cited by [`ModularCurve.XHDRLevel.exists_nodeEquiv_placeOfPoint_eq_and_eq_qExpFrobeniusPlaceModL`](thm.html#ModularCurve.XHDRLevel.exists_nodeEquiv_placeOfPoint_eq_and_eq_qExpFrobeniusPlaceModL), [`ModularCurve.XHDRLevel.exists_placeOfPoint_snd_pullback_comp_mem_ssPlacesQExp`](thm.html#ModularCurve.XHDRLevel.exists_placeOfPoint_snd_pullback_comp_mem_ssPlacesQExp) and [`ModularCurve.XHDRLevel.exists_snd_pullback_comp_eq_of_mem_ssPlacesQExp`](thm.html#ModularCurve.XHDRLevel.exists_snd_pullback_comp_eq_of_mem_ssPlacesQExp).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XHDRLevel_exists_placeOfPoint_fst_pullback_comp_eq_qExpFrobeniusPlaceModL.lean

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 400000

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve ModularCurve ModularCurve.XHDRLevel NeronModelInfra
open scoped MatrixGroups TensorProduct

theorem ModularCurve.XHDRLevel.exists_placeOfPoint_fst_pullback_comp_eq_qExpFrobeniusPlaceModL
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))

    (π : SchemeHomOver (toBase p (ΓM M H) hj) (toBase p (ΓN p M H hpM) hj))
    (iota0 : ↥(chartAlgFin p (ΓN p M H hpM) hj) →ₐ[R p] ↥(chartAlgFin p (ΓM M H) hj))
    (iota0_spec : ∀ b, (((iota0 b : ↥(chartAlgFin p (ΓM M H) hj)) : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ) =
      ((b : ↥(qExpFunctionFieldC ℚ (ΓN p M H hpM))) : LaurentSeries ℚ))
    (pi_chart : ιFin p (ΓM M H) hj ≫ π.1 = Spec.map (CommRingCat.ofHom iota0.toRingHom) ≫ ιFin p (ΓN p M H hpM) hj)

    (w : X p (ΓM M H) hj ≅ X p (ΓM M H) hj) (hw : w.hom ≫ toBase p (ΓM M H) hj = toBase p (ΓM M H) hj)
    (theta : ↥(chartAlgFin p (ΓM M H) hj) ≃ₐ[R p] ↥(chartAlgFin p (ΓM M H) hj))
    (htheta : ∀ b : ↥(chartAlgFin p (ΓN p M H hpM) hj),
      (((theta (iota0 b) : ↥(chartAlgFin p (ΓM M H) hj)) : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ) =
        qExpand ℚ p ((b : ↥(qExpFunctionFieldC ℚ (ΓN p M H hpM))) : LaurentSeries ℚ))

    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (IsLocalRing.ResidueField ↥A) p] [IsAlgClosed (IsLocalRing.ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))

    (comp : Fin 2 → (fibre (Γ := ΓN p M H hpM) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ) ⟶
      fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ)))
    (comp_over : ∀ i, comp i ≫ pullback.snd _ _ = pullback.snd _ _)
    (comp_isClosedImmersion : ∀ i, IsClosedImmersion (comp i))
    (comp_pi : comp 0 ≫ fibreMap π ((IsLocalRing.residue ↥A).comp ρ) = 𝟙 _)
    (comp_w : comp 0 ≫ fibreMap (overOfIso w hw) ((IsLocalRing.residue ↥A).comp ρ) = comp 1)

    (Mfib : CurveModel (IsLocalRing.ResidueField ↥A) ↥(qExpFunctionFieldC (IsLocalRing.ResidueField ↥A) (ΓN p M H hpM)))
    (efib : Mfib.C ⟶ fibre (Γ := ΓN p M H hpM) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ)) [IsIso efib]
    (hefib : efib ≫ pullback.snd _ _ = Mfib.toBase)
    [Mfib_chart_nonempty : Nonempty (Scheme.Opens.toScheme ((efib ≫ pullback.fst (toBase p (ΓN p M H hpM) hj)
      (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ)))) ⁻¹ᵁ ((ιFin p (ΓN p M H hpM) hj) ''ᵁ ⊤)))]
    (Mfib_pin : ∀ (b : ↥(chartAlgFin p (ΓN p M H hpM) hj)) (y : LaurentSeries ↥A),
    coeffMap A.subtype y = coeffEmb (AlgebraicClosure ℚ) (((b : ↥(qExpFunctionFieldC ℚ (ΓN p M H hpM))) : LaurentSeries ℚ)) →
    ((Mfib.ffEquiv.symm
        (Mfib.C.germToFunctionField
          ((efib ≫ pullback.fst (toBase p (ΓN p M H hpM) hj) (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ)))) ⁻¹ᵁ
            ((ιFin p (ΓN p M H hpM) hj) ''ᵁ ⊤))
          (((efib ≫ pullback.fst (toBase p (ΓN p M H hpM) hj) (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ)))).app
              ((ιFin p (ΓN p M H hpM) hj) ''ᵁ ⊤)).hom
            (((ιFin p (ΓN p M H hpM) hj).appIso ⊤).inv
              ((Scheme.ΓSpecIso (CommRingCat.of ↥(chartAlgFin p (ΓN p M H hpM) hj))).inv b))))
        : ↥(qExpFunctionFieldC (IsLocalRing.ResidueField ↥A) (ΓN p M H hpM))) : LaurentSeries (IsLocalRing.ResidueField ↥A)) =
      coeffMap (IsLocalRing.residue ↥A) y)

    (hfrob : ∀ P : closedPoints Mfib.C,
      ∃ h : (inv efib).base ((efib ≫ comp 1 ≫ fibreMap π ((IsLocalRing.residue ↥A).comp ρ)).base P.1) ∈ closedPoints Mfib.C,
        Mfib.placeOfPoint ⟨_, h⟩ =
          qExpFrobeniusPlaceModL (IsLocalRing.ResidueField ↥A) (ΓN p M H hpM) p (Mfib.placeOfPoint P)) :
    letI := ((IsLocalRing.residue ↥A).comp ρ).toAlgebra

    ∀ (c₀ : Spec (CommRingCat.of ((IsLocalRing.ResidueField ↥A) ⊗[R p] ↥(chartAlgFin p (ΓN p M H hpM) hj))) ⟶
          fibre (Γ := ΓN p M H hpM) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))
      (_ : c₀ ≫ pullback.fst _ _ =
        Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight
          (R := R p) (A := IsLocalRing.ResidueField ↥A) (B := ↥(chartAlgFin p (ΓN p M H hpM) hj))).toRingHom) ≫ ιFin p (ΓN p M H hpM) hj)
      (_ : c₀ ≫ pullback.snd _ _ =
        Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom
          (R := R p) (A := IsLocalRing.ResidueField ↥A) (B := ↥(chartAlgFin p (ΓN p M H hpM) hj)))))
      (c : Spec (CommRingCat.of ((IsLocalRing.ResidueField ↥A) ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj))) ⟶
          fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))
      (_ : c ≫ pullback.fst _ _ =
        Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight
          (R := R p) (A := IsLocalRing.ResidueField ↥A) (B := ↥(chartAlgFin p (ΓM M H) hj))).toRingHom) ≫ ιFin p (ΓM M H) hj)
      (_ : c ≫ pullback.snd _ _ =
        Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom
          (R := R p) (A := IsLocalRing.ResidueField ↥A) (B := ↥(chartAlgFin p (ΓM M H) hj)))))
      (_ : c ≫ fibreMap (overOfIso w hw) ((IsLocalRing.residue ↥A).comp ρ) =
        Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.map
          (AlgHom.id (IsLocalRing.ResidueField ↥A) (IsLocalRing.ResidueField ↥A)) theta.toAlgHom).toRingHom) ≫ c)

      (_ : ∀ n : ↥(pullback (comp 0) (comp 1)), (pullback.snd (comp 0) (comp 1)).base n ∈ Set.range c₀.base),
    ∀ (n : ↥(pullback (comp 0) (comp 1))) (h₁ : (inv efib).base ((pullback.snd (comp 0) (comp 1)).base n) ∈ closedPoints Mfib.C),
      ∃ h₀ : (inv efib).base ((pullback.fst (comp 0) (comp 1)).base n) ∈ closedPoints Mfib.C,
        Mfib.placeOfPoint ⟨_, h₀⟩ =
          qExpFrobeniusPlaceModL (IsLocalRing.ResidueField ↥A) (ΓN p M H hpM) p (Mfib.placeOfPoint ⟨_, h₁⟩) := by sorry
