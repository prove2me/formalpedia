-- Prove2me | Theorems.Thm_ModularCurve_XHDRLevel_exists_nodeEquiv_placeOfPoint_eq_and_eq_qExpFrobeniusPlaceModL
-- name    : ModularCurve.XHDRLevel.exists_nodeEquiv_placeOfPoint_eq_and_eq_qExpFrobeniusPlaceModL
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.68297+00:00
-- url     : https://prove2.me/theorems/13ba0f62-027d-5df0-8a5c-7667daac9c9f
-- title:
--   Crossings of the Deligne–Rapoport fibre enumerated by supersingular places
-- statement:
--   Fix a prime $p$ and $M \neq 0$ with $p \mid M$ and $p^2 \nmid M$, and a subgroup $H \le (\mathbb{Z}/M)^\times$ containing every unit that reduces to $1$ in $(\mathbb{Z}/(M/p))^\times$; assume $j$, as a Laurent series `jqModC ℚ`, lies in the $q$-expansion function field of the full group. The data consist of: a morphism $\pi$ of the two-chart integral models $X_p(\Gamma_M)\to X_p(\Gamma_N)$ over $\operatorname{Spec} R_p$; an $R_p$-algebra map `iota0` between the $j$-finite chart algebras which is the identity on $q$-expansions and is compatible with $\pi$ over the finite chart; an isomorphism $w$ of $X_p(\Gamma_M)$ over the base together with an $R_p$-algebra automorphism $\theta$ of its finite chart algebra such that $\theta \circ \mathrm{iota0}$ acts on $q$-expansions as $q \mapsto q^p$ (the operator `qExpand ℚ p`); a valuation subring $A$ of $\overline{\mathbb{Q}}$ with $p$ in its nonunits, with algebraically closed residue field $\kappa$ of characteristic $p$, and a ring map $\rho : R_p \to A$ lifting $R_p \to \overline{\mathbb{Q}}$; two closed immersions $\mathrm{comp}\,0, \mathrm{comp}\,1$ of the $\Gamma_N$-fibre over $\kappa$ into the $\Gamma_M$-fibre, both over the base, with $\mathrm{comp}\,0$ followed by the fibre map of $\pi$ the identity and $\mathrm{comp}\,0$ followed by the fibre map of $w$ equal to $\mathrm{comp}\,1$; a curve model `Mfib` over $\kappa$ with function field $F' =$ `qExpFunctionFieldC κ (ΓN p M H hpM)` (a proper smooth integral curve, an identification of its function field with $F'$, and a bijection `placeOfPoint` from closed points to places compatible with stalks) together with an isomorphism `efib` of `Mfib.C` with the $\Gamma_N$-fibre over the base; the hypothesis that the preimage of the $j$-finite chart is nonempty and the pinning condition that for each chart element $b$ and each Laurent series $y$ over $A$ whose image in $\overline{\mathbb{Q}}$-coefficients is the $q$-expansion of $b$, the function-field element obtained from the germ of $b$ has $q$-expansion the coefficientwise reduction of $y$; and the Frobenius clause: for every closed point $P$ of `Mfib.C`, the point obtained by transporting $P$ through $\mathrm{comp}\,1$ followed by the fibre map of $\pi$ back along `efib` is closed with place `qExpFrobeniusPlaceModL κ ΓN p` applied to the place of $P$. Give, in addition, chart sections $c_0$ and $c$ of the two fibres from $\operatorname{Spec}$ of $\kappa \otimes_{R_p} (\text{finite chart algebra})$ at levels $\Gamma_N$ and $\Gamma_M$ respectively, each compatible with the two projections via the right and left inclusions into the tensor product, with $c$ intertwining the fibre map of $w$ with $\operatorname{Spec}$ of $\mathrm{id} \otimes \theta$, and assume every point of the fibre product of $\mathrm{comp}\,0$ and $\mathrm{comp}\,1$ lies in the image of $c_0$ on points. The conclusion is that there is a bijection `nodeEquiv` from the underlying set of that fibre product onto `ssPlacesQExp κ ΓN p`, the set of places $v$ of $F'$ for which some $x \in F'$ with $q$-expansion `jqModC κ` satisfies $v(x) = a$ for some $a$ in the supersingular $j$-set, such that for every point $n$: transporting the second projection of $n$ back along `efib` gives a closed point of `Mfib.C` whose place is `nodeEquiv n`, and transporting the first projection gives a closed point whose place is `qExpFrobeniusPlaceModL κ ΓN p` applied to `nodeEquiv n`.
--
--   This is the Deligne–Rapoport description of the fibre at $p$ of the modular curve of level $H$ with $p$ exactly dividing $M$: the fibre is two copies of the lower-level curve glued along the supersingular points, one copy meeting the other through the Frobenius twist of the corresponding place. It is used by [`ModularCurve.exists_xHDRModelAtP_atkinLehner_generic_chart`](thm.html#ModularCurve.exists_xHDRModelAtP_atkinLehner_generic_chart) to assemble the model at $p$ together with its Atkin–Lehner involution, the crossings being recorded as the supersingular places of the $q$-expansion function field in characteristic $p$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XHDRLevel_exists_nodeEquiv_placeOfPoint_eq_and_eq_qExpFrobeniusPlaceModL.lean

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 400000

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve ModularCurve.XHDRLevel NeronModelInfra
open ModularCurve hiding nodeEquiv
open scoped MatrixGroups TensorProduct

theorem ModularCurve.XHDRLevel.exists_nodeEquiv_placeOfPoint_eq_and_eq_qExpFrobeniusPlaceModL
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
    ∃ nodeEquiv : ↥(pullback (comp 0) (comp 1)) ≃ ↥(ssPlacesQExp (IsLocalRing.ResidueField ↥A) (ΓN p M H hpM) p),
      ∀ n : ↥(pullback (comp 0) (comp 1)),
        (∃ h : (inv efib).base ((pullback.snd (comp 0) (comp 1)).base n) ∈ closedPoints Mfib.C,
            Mfib.placeOfPoint ⟨_, h⟩ =
              ((nodeEquiv n : ↥(ssPlacesQExp (IsLocalRing.ResidueField ↥A) (ΓN p M H hpM) p)) :
                Place (IsLocalRing.ResidueField ↥A) ↥(qExpFunctionFieldC (IsLocalRing.ResidueField ↥A) (ΓN p M H hpM)))) ∧
        (∃ h : (inv efib).base ((pullback.fst (comp 0) (comp 1)).base n) ∈ closedPoints Mfib.C,
            Mfib.placeOfPoint ⟨_, h⟩ =
              qExpFrobeniusPlaceModL (IsLocalRing.ResidueField ↥A) (ΓN p M H hpM) p
                ((nodeEquiv n : ↥(ssPlacesQExp (IsLocalRing.ResidueField ↥A) (ΓN p M H hpM) p)) :
                  Place (IsLocalRing.ResidueField ↥A) ↥(qExpFunctionFieldC (IsLocalRing.ResidueField ↥A) (ΓN p M H hpM)))) := by sorry
