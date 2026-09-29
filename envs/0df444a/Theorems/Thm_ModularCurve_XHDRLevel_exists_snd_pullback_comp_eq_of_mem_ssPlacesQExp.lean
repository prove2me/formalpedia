-- Prove2me | Theorems.Thm_ModularCurve_XHDRLevel_exists_snd_pullback_comp_eq_of_mem_ssPlacesQExp
-- name    : ModularCurve.XHDRLevel.exists_snd_pullback_comp_eq_of_mem_ssPlacesQExp
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.68297+00:00
-- url     : https://prove2.me/theorems/d59ed15d-af9e-593f-befc-9cd44819367b
-- title:
--   Supersingular places come from crossings of the two components
-- statement:
--   Fix a prime $p$ and a level $M$ with $p \mid M$ but $p^2 \nmid M$, a subgroup $H \le (\mathbb{Z}/M)^\times$ containing every unit that reduces to $1$ in $(\mathbb{Z}/(M/p))^\times$, and a witness $hj$ that the $q$-series `jqModC ℚ` lies in the $q$-expansion function field of the full group over $\mathbb{Q}$. The data are: a morphism $\pi$ from $X_p(\Gamma_M)$ to $X_p(\Gamma_N)$ over $\operatorname{Spec}(R_p)$; an $R_p$-algebra map $\iota_0$ between the corresponding $j$-finite chart algebras which is the identity on Laurent series, compatible with $\pi$ on the charts via `pi_chart`; an automorphism $w$ of $X_p(\Gamma_M)$ over the base together with an $R_p$-algebra automorphism $\theta$ of the $\Gamma_M$ chart algebra such that $\theta \circ \iota_0$ induces $q \mapsto q^p$ (`qExpand ℚ p`) on Laurent series; a valuation subring $A$ of $\overline{\mathbb{Q}}$ with $p$ a nonunit, whose residue field $\kappa$ is algebraically closed of characteristic $p$, and $\rho : R_p \to A$ compatible with the structure map to $\overline{\mathbb{Q}}$; two closed immersions $\mathrm{comp}\,0, \mathrm{comp}\,1$ from the $\Gamma_N$-fibre over $\kappa$ to the $\Gamma_M$-fibre, both over $\operatorname{Spec}\kappa$, with $\mathrm{comp}\,0$ a section of the map induced by $\pi$ and $\mathrm{comp}\,1$ its composite with the map induced by $w$; a curve model `Mfib` over $\kappa$ with function field the $q$-expansion function field of $\Gamma_N$ over $\kappa$, an isomorphism $e$ from its underlying scheme to the $\Gamma_N$-fibre over the base, a nonemptiness assumption on the chart preimage, a normalisation `Mfib_pin` identifying germs of chart functions with reductions of Laurent series, and `hfrob` saying that transporting a closed point $P$ along $e$, $\mathrm{comp}\,1$ and the map induced by $\pi$ yields a closed point whose place is `qExpFrobeniusPlaceModL` applied to the place of $P$. Then, given affine coordinate charts $c_0$ and $c$ on the two fibres, i.e. morphisms out of $\operatorname{Spec}(\kappa \otimes_{R_p} \text{chart})$ whose composites with the two pullback projections are the Spec of the right and left inclusions, with $c$ moreover intertwining the map induced by $w$ with $\mathrm{id} \otimes \theta$, and assuming every point of the fibre product of $\mathrm{comp}\,0$ and $\mathrm{comp}\,1$ has its second projection in the image of $c_0$, the conclusion is: for every place $y$ in `ssPlacesQExp κ (ΓN p M H hpM) p`, that is every place $v$ of the $q$-expansion function field admitting $x$ with Laurent series `jqModC κ` and a value $a \in$ `ssJSet p` at $x$, there is a point $n$ of the fibre product of $\mathrm{comp}\,0$ and $\mathrm{comp}\,1$ whose image under the second projection, transported back by $e^{-1}$, is a closed point of `Mfib.C` whose place equals $y$.
--
--   This is the surjectivity half of the Deligne–Rapoport description of the fibre at $p$ of the modular curve of level $M$ with $p \parallel M$: every supersingular place of the characteristic-$p$ $q$-expansion function field is the coordinate, on the component indexed by $\Gamma_N$, of a crossing point of the two components. It is used in the construction of the bijection between crossings and supersingular places recorded in [`ModularCurve.XHDRLevel.exists_nodeEquiv_placeOfPoint_eq_and_eq_qExpFrobeniusPlaceModL`](thm.html#ModularCurve.XHDRLevel.exists_nodeEquiv_placeOfPoint_eq_and_eq_qExpFrobeniusPlaceModL).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XHDRLevel_exists_snd_pullback_comp_eq_of_mem_ssPlacesQExp.lean

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

theorem ModularCurve.XHDRLevel.exists_snd_pullback_comp_eq_of_mem_ssPlacesQExp
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
    ∀ y : ↥(ssPlacesQExp (IsLocalRing.ResidueField ↥A) (ΓN p M H hpM) p),
      ∃ (n : ↥(pullback (comp 0) (comp 1))) (h : (inv efib).base ((pullback.snd (comp 0) (comp 1)).base n) ∈ closedPoints Mfib.C),
        Mfib.placeOfPoint ⟨_, h⟩ = (y : Place (IsLocalRing.ResidueField ↥A) ↥(qExpFunctionFieldC (IsLocalRing.ResidueField ↥A) (ΓN p M H hpM))) := by sorry
