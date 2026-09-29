-- Prove2me | Theorems.Thm_ModularCurve_XHDRLevel_exists_chart_frobenius_comp_one_fibreMap_pi_of_liesOverPrime
-- name    : ModularCurve.XHDRLevel.exists_chart_frobenius_comp_one_fibreMap_pi_of_liesOverPrime
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.68297+00:00
-- url     : https://prove2.me/theorems/aed4dce2-ed81-588a-a025-e63c93604a85
-- title:
--   Chart-level Frobenius for comp₁ followed by π
-- statement:
--   Fix a prime $p$ and $M \neq 0$ with $p \mid M$ and $p^2 \nmid M$, and a subgroup $H \le (\mathbb{Z}/M)^\times$ containing every unit whose image under `ZMod.unitsMap` for $M/p \mid M$ is $1$; assume $j$, as the Laurent series `jqModC ℚ`, lies in the $q$-expansion function field of the full modular group, so that the two-chart integral models `X p Γ hj` over $\operatorname{Spec}(R p)$ are available for the groups `ΓM M H` and `ΓN p M H hpM`. Given: a morphism $\pi$ of the model for `ΓM M H` to that for `ΓN p M H hpM` over $\operatorname{Spec}(R p)$; an $R p$-algebra map $\iota_0$ between the corresponding $j$-finite chart algebras (subalgebras of integral elements over the adjunction of $j$) which is the identity on $q$-expansions, and which computes $\pi$ on the $j$-finite charts $\iota_{\mathrm{Fin}}$; an isomorphism $w$ of the `ΓM M H` model over the base and an $R p$-algebra automorphism $\theta$ of its $j$-finite chart algebra with $\theta(\iota_0 b)(q) = b(q^p)$ for all chart elements $b$; a valuation subring $A$ of $\overline{\mathbb{Q}}$ with $p$ a non-unit of $A$, whose residue field $\kappa$ has characteristic $p$ and is algebraically closed, and a ring map $\rho : R p \to A$ lifting the structure map to $\overline{\mathbb{Q}}$; and two morphisms $\mathrm{comp}_0, \mathrm{comp}_1$ from the $\kappa$-fibre (the pullback of `toBase` along $\operatorname{Spec}$ of $\kappa$) of the `ΓN p M H hpM` model to that of the `ΓM M H` model, each commuting with the projections to $\operatorname{Spec}\kappa$ and each a closed immersion, such that $\mathrm{comp}_0$ followed by the fibre map of $\pi$ is the identity and $\mathrm{comp}_0$ followed by the fibre map of $w$ is $\mathrm{comp}_1$. Then, for every chart $c_0 : \operatorname{Spec}(\kappa \otimes_{R p} \mathcal{O}_{\mathrm{fin}}(\Gamma_N))$ and every chart $c : \operatorname{Spec}(\kappa \otimes_{R p} \mathcal{O}_{\mathrm{fin}}(\Gamma_M))$ into the respective $\kappa$-fibres which are compatible with the $j$-finite charts and with the projections to $\operatorname{Spec}\kappa$ (via `includeRight`, `includeLeftRingHom`), and with $c$ intertwining the fibre map of $w$ with $\operatorname{Spec}$ of $\mathrm{id}_\kappa \otimes \theta$, there exists a $\kappa$-algebra endomorphism $\varphi$ of $\kappa \otimes_{R p} \mathcal{O}_{\mathrm{fin}}(\Gamma_N)$ with $\varphi(1 \otimes b) = (1 \otimes b)^p$ for all chart elements $b$, and such that $c_0$ followed by $\mathrm{comp}_1$ followed by the fibre map of $\pi$ equals $\operatorname{Spec}(\varphi)$ followed by $c_0$.
--
--   This is the chart-level form of the Deligne–Rapoport description of the mod-$p$ fibre of a modular curve at a prime exactly dividing the level: on the second component, obtained from the first by the Atkin–Lehner involution, the forgetful map to the lower level is the $p$-power Frobenius. It is used in assembling the Néron-model property bundle for the model of $X_H(M)$ at $p$, via [`ModularCurve.XHDRLevel.comp1_pi_place_and_pi_w_comp0_place_of_chart_atkinLehner`](thm.html#ModularCurve.XHDRLevel.comp1_pi_place_and_pi_w_comp0_place_of_chart_atkinLehner).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XHDRLevel_exists_chart_frobenius_comp_one_fibreMap_pi_of_liesOverPrime.lean

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 400000

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve ModularCurve NeronModelInfra
open ModularCurve.XHDRLevel
open scoped MatrixGroups TensorProduct

theorem ModularCurve.XHDRLevel.exists_chart_frobenius_comp_one_fibreMap_pi_of_liesOverPrime
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
    (comp_w : comp 0 ≫ fibreMap (overOfIso w hw) ((IsLocalRing.residue ↥A).comp ρ) = comp 1) :
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
          (AlgHom.id (IsLocalRing.ResidueField ↥A) (IsLocalRing.ResidueField ↥A)) theta.toAlgHom).toRingHom) ≫ c),
    ∃ φ : (IsLocalRing.ResidueField ↥A) ⊗[R p] ↥(chartAlgFin p (ΓN p M H hpM) hj) →ₐ[IsLocalRing.ResidueField ↥A]
        (IsLocalRing.ResidueField ↥A) ⊗[R p] ↥(chartAlgFin p (ΓN p M H hpM) hj),
      (∀ b : ↥(chartAlgFin p (ΓN p M H hpM) hj),
        φ ((1 : IsLocalRing.ResidueField ↥A) ⊗ₜ[R p] b) = ((1 : IsLocalRing.ResidueField ↥A) ⊗ₜ[R p] b) ^ p) ∧
      c₀ ≫ comp 1 ≫ fibreMap π ((IsLocalRing.residue ↥A).comp ρ) = Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ c₀ := by sorry
