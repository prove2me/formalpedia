-- Prove2me | Theorems.Thm_ModularCurve_XHDRLevel_exists_placeOfPoint_snd_pullback_comp_mem_ssPlacesQExp
-- name    : ModularCurve.XHDRLevel.exists_placeOfPoint_snd_pullback_comp_mem_ssPlacesQExp
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.68297+00:00
-- url     : https://prove2.me/theorems/e6689eb6-5e7a-5155-b6f0-0f806c28eafc
-- title:
--   Crossings of the fibre lie at supersingular places
-- statement:
--   Fix a prime $p$ and $M \neq 0$ with $p \mid M$ and $p^2 \nmid M$, a subgroup $H \le (\mathbb{Z}/M)^\times$ containing every unit that is trivial modulo $M/p$, and a witness `hj` that the Laurent series `jqModC ℚ` lies in the field $\mathcal{F}_{\mathbb{Q}}(\mathrm{SL}_2(\mathbb{Z}))$ generated over $\mathbb{Q}$ by ratios of integral $q$-expansions of modular forms. The data are: a morphism $\pi$ from the two-chart integral model `X p (ΓM M H) hj` to `X p (ΓN p M H hpM) hj` commuting with the structure morphisms `toBase` to $\operatorname{Spec} R_p$; an `R p`-algebra map `iota0` between the finite-chart algebras inducing the identity on $q$-expansions, compatible with $\pi$ on the finite charts via `pi_chart`; a self-isomorphism $w$ of `X p (ΓM M H) hj` over the base, together with an `R p`-algebra automorphism `theta` of the level-$\Gamma_M$ finite chart algebra sending `iota0 b` to the series `qExpand ℚ p` applied to the $q$-expansion of $b$, i.e. the substitution $q \mapsto q^p$; a valuation subring $A$ of $\overline{\mathbb{Q}}$ with $p$ in its nonunits, with algebraically closed residue field $k$ of characteristic $p$, and a lift $\rho : R_p \to A$ of the structure map; two morphisms `comp 0`, `comp 1` from the $k$-fibre at level $\Gamma_N$ to the $k$-fibre at level $\Gamma_M$, each a closed immersion over $\operatorname{Spec} k$, with `comp 0` a section of the reduction of $\pi$ and `comp 1` its composite with the reduction of $w$; a `CurveModel` $M_{\mathrm{fib}}$ over $k$ with function field $\mathcal{F}_k(\Gamma_N)$, i.e. an integral scheme, proper and smooth of relative dimension $1$ over $\operatorname{Spec} k$, with an isomorphism of $\mathcal{F}_k(\Gamma_N)$ onto its function field and a bijection `placeOfPoint` from closed points to places; an isomorphism `efib` of $M_{\mathrm{fib}}.C$ with the $\Gamma_N$-fibre over $\operatorname{Spec} k$, with non-empty finite-chart preimage, and the dictionary `Mfib_pin` identifying the function attached by `efib` to a chart element $b$ with the coefficientwise reduction of any Laurent series over $A$ lifting the $q$-expansion of $b$; and `hfrob`, asserting that `efib ≫ comp 1` followed by the reduction of $\pi$ moves closed points so that the place of the image is `qExpFrobeniusPlaceModL` of the place of the source. Given, for the $R_p$-algebra structure on $k$ induced by the residue map after $\rho$, morphisms $c_0$ and $c$ from $\operatorname{Spec}$ of $k \otimes_{R_p} (\text{finite chart algebra})$ at levels $\Gamma_N$ and $\Gamma_M$ into the respective $k$-fibres, each compatible with the two pullback projections via `includeRight` followed by `ιFin` and via `includeLeftRingHom`, with $c$ intertwining the reduction of $w$ with $\operatorname{Spec}$ of $\mathrm{id} \otimes$ `theta`, and assuming every point of the fibre product of `comp 0` and `comp 1` has its second projection in the image of $c_0$ on points, the conclusion is that for every point $n$ of that fibre product the image of `pullback.snd n` under the inverse of `efib` is a closed point of $M_{\mathrm{fib}}.C$ and its place lies in `ssPlacesQExp k (ΓN p M H hpM) p`: there are an element $x$ of $\mathcal{F}_k(\Gamma_N)$ whose Laurent series is `jqModC k` and a scalar $a \in k$ with $x$ taking the value $a$ at that place and $a$ a supersingular $j$-invariant for $p$.
--
--   This is the supersingularity half of the Deligne–Rapoport description of the fibre at $p$ of the modular curve of level $H$ when $p$ exactly divides $M$: the two components of the fibre, here presented as the closed immersions `comp 0` and `comp 1`, meet only above supersingular $j$-invariants. It is the first step in the construction of the node dictionary together with the Frobenius relation between the places attached to the two branches at a crossing.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XHDRLevel_exists_placeOfPoint_snd_pullback_comp_mem_ssPlacesQExp.lean

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

theorem ModularCurve.XHDRLevel.exists_placeOfPoint_snd_pullback_comp_mem_ssPlacesQExp
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
    ∀ n : ↥(pullback (comp 0) (comp 1)),
      ∃ h : (inv efib).base ((pullback.snd (comp 0) (comp 1)).base n) ∈ closedPoints Mfib.C,
        Mfib.placeOfPoint ⟨_, h⟩ ∈ ssPlacesQExp (IsLocalRing.ResidueField ↥A) (ΓN p M H hpM) p := by sorry
