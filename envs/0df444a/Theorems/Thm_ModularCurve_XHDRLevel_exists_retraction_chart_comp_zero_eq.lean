-- Prove2me | Theorems.Thm_ModularCurve_XHDRLevel_exists_retraction_chart_comp_zero_eq
-- name    : ModularCurve.XHDRLevel.exists_retraction_chart_comp_zero_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.68297+00:00
-- url     : https://prove2.me/theorems/853425e3-9aca-5448-b68d-c38f8245378f
-- title:
--   Chart retraction from a section of the degeneracy map mod p
-- statement:
--   Fix a prime $p$, a non-zero natural number $M$ with $p \mid M$ and $p^2 \nmid M$, a subgroup $H \le (\mathbb{Z}/M)^\times$, and assume $j$'s $q$-expansion `jqModC ℚ` lies in the $q$-expansion function field of level $\mathrm{SL}(2,\mathbb{Z})$. Let $\pi$ be a morphism $X_{p,\Gamma_M(M,H)} \to X_{p,\Gamma_N(p,M,H)}$ of two-chart integral models commuting with their structure morphisms to $\operatorname{Spec} R_p$, and let $\iota_0$ be an $R_p$-algebra map between the $j$-finite chart algebras which, after both are viewed inside Laurent series over $\mathbb{Q}$, is the identity on $q$-expansions, and suppose $\pi$ restricted along the $j$-finite chart inclusions is $\operatorname{Spec}\iota_0$. Let $\kappa$ be an algebraically closed field of characteristic $p$ over $R_p$, and let $c_0$, $c$ be the $j$-finite charts of the two fibres over $\kappa$, i.e. morphisms from $\operatorname{Spec}(\kappa \otimes_{R_p} \mathcal{O})$ into the respective pullbacks, whose compositions with the two projections are $\operatorname{Spec}$ of the right and left inclusions into the tensor product (the first followed by the chart inclusion). Let $\mathrm{comp}\,0, \mathrm{comp}\,1$ be closed immersions from the $\Gamma_N$-fibre to the $\Gamma_M$-fibre over $\operatorname{Spec}\kappa$ with $(\text{fibre of }\pi) \circ \mathrm{comp}\,0 = \mathrm{id}$. Then there is a $\kappa$-algebra homomorphism $\sigma_0 : \kappa \otimes_{R_p} \mathcal{O}_{\Gamma_M} \to \kappa \otimes_{R_p} \mathcal{O}_{\Gamma_N}$ with $\sigma_0 \circ (\mathrm{id}_\kappa \otimes \iota_0) = \mathrm{id}$ and $\mathrm{comp}\,0 \circ c_0 = c \circ \operatorname{Spec}\sigma_0$, and moreover, for every isomorphism $w$ of $X_{p,\Gamma_M(M,H)}$ over the base and every $R_p$-algebra automorphism $\theta$ of the $j$-finite chart algebra such that the induced map on fibres satisfies $(\text{fibre of } w) \circ c = c \circ \operatorname{Spec}(\mathrm{id}_\kappa \otimes \theta)$ and $(\text{fibre of } w) \circ \mathrm{comp}\,0 = \mathrm{comp}\,1$, one has $\mathrm{comp}\,1 \circ c_0 = c \circ \operatorname{Spec}(\sigma_0 \circ (\mathrm{id}_\kappa \otimes \theta))$.
--
--   This is the $\Gamma_H(M)$ form of the statement that a component of the mod-$p$ fibre carrying a section of the degeneracy map is, on the $j$-finite chart, the spectrum of a retraction of chart algebras, the algebraic shadow of the Deligne–Rapoport description of the fibre at $p$ of a modular curve of level divisible exactly once by $p$. It feeds the later analysis of the two components of the fibre, in particular the identification of one of them via Frobenius on the chart and the comparison of $\mathrm{comp}\,1$ with the Atkin–Lehner twist of $\mathrm{comp}\,0$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XHDRLevel_exists_retraction_chart_comp_zero_eq.lean

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve ModularCurve ModularCurve.XHDRLevel NeronModelInfra
open scoped MatrixGroups TensorProduct

set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem ModularCurve.XHDRLevel.exists_retraction_chart_comp_zero_eq
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))

    (π : SchemeHomOver (toBase p (ΓM M H) hj) (toBase p (ΓN p M H hpM) hj))
    (iota0 : ↥(chartAlgFin p (ΓN p M H hpM) hj) →ₐ[R p] ↥(chartAlgFin p (ΓM M H) hj))
    (iota0_spec : ∀ b, (((iota0 b : ↥(chartAlgFin p (ΓM M H) hj)) : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ) =
      ((b : ↥(qExpFunctionFieldC ℚ (ΓN p M H hpM))) : LaurentSeries ℚ))
    (pi_chart : ιFin p (ΓM M H) hj ≫ π.1 = Spec.map (CommRingCat.ofHom iota0.toRingHom) ≫ ιFin p (ΓN p M H hpM) hj)

    (κ : Type) [Field κ] [CharP κ p] [IsAlgClosed κ] [Algebra (R p) κ]

    (c₀ : Spec (CommRingCat.of (κ ⊗[R p] ↥(chartAlgFin p (ΓN p M H hpM) hj))) ⟶ fibre (Γ := ΓN p M H hpM) (hj := hj) (algebraMap (R p) κ))
    (hc₀fst : c₀ ≫ pullback.fst _ _ =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight
        (R := R p) (A := κ) (B := ↥(chartAlgFin p (ΓN p M H hpM) hj))).toRingHom) ≫ ιFin p (ΓN p M H hpM) hj)
    (hc₀snd : c₀ ≫ pullback.snd _ _ =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom
        (R := R p) (A := κ) (B := ↥(chartAlgFin p (ΓN p M H hpM) hj)))))
    (c : Spec (CommRingCat.of (κ ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj))) ⟶ fibre (Γ := ΓM M H) (hj := hj) (algebraMap (R p) κ))
    (hcfst : c ≫ pullback.fst _ _ =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight
        (R := R p) (A := κ) (B := ↥(chartAlgFin p (ΓM M H) hj))).toRingHom) ≫ ιFin p (ΓM M H) hj)
    (hcsnd : c ≫ pullback.snd _ _ =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom
        (R := R p) (A := κ) (B := ↥(chartAlgFin p (ΓM M H) hj)))))

    (comp : Fin 2 → (fibre (Γ := ΓN p M H hpM) (hj := hj) (algebraMap (R p) κ) ⟶ fibre (Γ := ΓM M H) (hj := hj) (algebraMap (R p) κ)))
    (comp_over : ∀ i, comp i ≫ pullback.snd _ _ = pullback.snd _ _)
    (comp_isClosedImmersion : ∀ i, IsClosedImmersion (comp i))
    (comp_pi : comp 0 ≫ fibreMap π (algebraMap (R p) κ) = 𝟙 _) :
    ∃ σ₀ : κ ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj) →ₐ[κ] κ ⊗[R p] ↥(chartAlgFin p (ΓN p M H hpM) hj),
      (∀ z, σ₀ (Algebra.TensorProduct.map (AlgHom.id κ κ) iota0 z) = z) ∧
      c₀ ≫ comp 0 = Spec.map (CommRingCat.ofHom σ₀.toRingHom) ≫ c ∧

      (∀ (w : X p (ΓM M H) hj ≅ X p (ΓM M H) hj) (hw : w.hom ≫ toBase p (ΓM M H) hj = toBase p (ΓM M H) hj)
        (theta : ↥(chartAlgFin p (ΓM M H) hj) ≃ₐ[R p] ↥(chartAlgFin p (ΓM M H) hj)),
        c ≫ fibreMap (overOfIso w hw) (algebraMap (R p) κ) =
          Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.map (AlgHom.id κ κ) theta.toAlgHom).toRingHom) ≫ c →
        comp 0 ≫ fibreMap (overOfIso w hw) (algebraMap (R p) κ) = comp 1 →
        c₀ ≫ comp 1 =
          Spec.map (CommRingCat.ofHom (σ₀.comp (Algebra.TensorProduct.map (AlgHom.id κ κ) theta.toAlgHom)).toRingHom) ≫ c) := by sorry
