-- Prove2me | Theorems.Thm_ModularCurve_XHDRLevel_exists_retraction_chartInf_comp_zero_eq_of_dvd
-- name    : ModularCurve.XHDRLevel.exists_retraction_chartInf_comp_zero_eq_of_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.68297+00:00
-- url     : https://prove2.me/theorems/22468ac9-81f4-5f36-8bed-57698db06739
-- title:
--   Pole-chart retraction for the mod p fibre of X_H(M)
-- statement:
--   Fix a prime $p$ and a nonzero natural number $M$ with $p \mid M$, a subgroup $H \le (\mathbb{Z}/M)^\times$, and a witness $hj$ that the Laurent series `jqModC ℚ` lies in the $q$-expansion function field $\mathbb{Q}(\Gamma)$ for $\Gamma = \mathrm{SL}_2(\mathbb{Z})$, so that the two-chart integral models `X p Γ hj` over $\operatorname{Spec} R_p$ are available for the congruence subgroups `ΓM M H` and `ΓN p M H hpM`. Assume given: a morphism $\pi$ from the model at level `ΓM M H` to the one at level `ΓN p M H hpM` commuting with the structure morphisms `toBase` to $\operatorname{Spec} R_p$; an $R_p$-algebra map $\iota_\infty$ from the pole-chart algebra `chartAlgInf` at level `ΓN p M H hpM` to the one at level `ΓM M H` which preserves Laurent expansions, i.e. the Laurent series of $\iota_\infty b$ equals that of $b$ for all $b$; and the hypothesis that $\iota_{\infty}$ computes $\pi$ on the pole charts, namely `ιInf` at level `ΓM M H` followed by $\pi$ equals $\operatorname{Spec}(\iota_\infty)$ followed by `ιInf` at level `ΓN p M H hpM`. Let $\kappa$ be an algebraically closed field of characteristic $p$ which is an $R_p$-algebra, and write `fibre` for the pullback of `toBase` along $\operatorname{Spec}$ of $R_p \to \kappa$. Let $c_0$, respectively $c$, be morphisms from $\operatorname{Spec}(\kappa \otimes_{R_p} \mathcal{O}_\infty)$, with $\mathcal{O}_\infty$ the pole-chart algebra at level `ΓN p M H hpM`, respectively `ΓM M H`, to the corresponding fibre, whose first pullback projection is $\operatorname{Spec}$ of the right inclusion followed by `ιInf`, and whose second projection is $\operatorname{Spec}$ of the left inclusion $\kappa \to \kappa \otimes_{R_p} \mathcal{O}_\infty$. Finally let $\mathrm{comp} \colon \mathrm{Fin}\,2 \to$ morphisms from the fibre at level `ΓN p M H hpM` to the fibre at level `ΓM M H`, each compatible with the projection to $\operatorname{Spec}\kappa$ and a closed immersion, and such that $\mathrm{comp}\,0$ followed by `fibreMap π` is the identity. The conclusion asserts the existence of a $\kappa$-algebra homomorphism $\sigma_0 \colon \kappa \otimes_{R_p} \mathcal{O}_\infty^{(M)} \to \kappa \otimes_{R_p} \mathcal{O}_\infty^{(N)}$ such that $\sigma_0 \circ (\mathrm{id}_\kappa \otimes \iota_\infty)$ is the identity and $c_0$ followed by $\mathrm{comp}\,0$ equals $\operatorname{Spec}(\sigma_0)$ followed by $c$.
--
--   This is the pole-chart ($j = \infty$) counterpart of the finite-chart statement describing the component of the mod $p$ fibre of the modular curve at level $H \le (\mathbb{Z}/M)^\times$ that is a section of the degeneracy map: over the pole chart that component is cut out by the kernel of an explicit retraction $\sigma_0$ of $\kappa \otimes \iota_\infty$. It is used in the analysis of the mod $p$ fibre, by [`ModularCurve.XHDRModelAtP.mem_range_comp_zero_iff_map_ker_le`](thm.html#ModularCurve.XHDRModelAtP.mem_range_comp_zero_iff_map_ker_le) and by [`ModularCurve.XHDRModelAtP.subsingleton_minimalPrimes_le_ker_cusp`](thm.html#ModularCurve.XHDRModelAtP.subsingleton_minimalPrimes_le_ker_cusp).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XHDRLevel_exists_retraction_chartInf_comp_zero_eq_of_dvd.lean

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

theorem ModularCurve.XHDRLevel.exists_retraction_chartInf_comp_zero_eq_of_dvd
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))

    (π : SchemeHomOver (toBase p (ΓM M H) hj) (toBase p (ΓN p M H hpM) hj))
    (iotaInf : ↥(chartAlgInf p (ΓN p M H hpM) hj) →ₐ[R p] ↥(chartAlgInf p (ΓM M H) hj))
    (iotaInf_spec : ∀ b, (((iotaInf b : ↥(chartAlgInf p (ΓM M H) hj)) : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ) =
      ((b : ↥(qExpFunctionFieldC ℚ (ΓN p M H hpM))) : LaurentSeries ℚ))
    (pi_chartInf : ιInf p (ΓM M H) hj ≫ π.1 = Spec.map (CommRingCat.ofHom iotaInf.toRingHom) ≫ ιInf p (ΓN p M H hpM) hj)

    (κ : Type) [Field κ] [CharP κ p] [IsAlgClosed κ] [Algebra (R p) κ]

    (c₀ : Spec (CommRingCat.of (κ ⊗[R p] ↥(chartAlgInf p (ΓN p M H hpM) hj))) ⟶ fibre (Γ := ΓN p M H hpM) (hj := hj) (algebraMap (R p) κ))
    (hc₀fst : c₀ ≫ pullback.fst _ _ =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight
        (R := R p) (A := κ) (B := ↥(chartAlgInf p (ΓN p M H hpM) hj))).toRingHom) ≫ ιInf p (ΓN p M H hpM) hj)
    (hc₀snd : c₀ ≫ pullback.snd _ _ =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom
        (R := R p) (A := κ) (B := ↥(chartAlgInf p (ΓN p M H hpM) hj)))))
    (c : Spec (CommRingCat.of (κ ⊗[R p] ↥(chartAlgInf p (ΓM M H) hj))) ⟶ fibre (Γ := ΓM M H) (hj := hj) (algebraMap (R p) κ))
    (hcfst : c ≫ pullback.fst _ _ =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight
        (R := R p) (A := κ) (B := ↥(chartAlgInf p (ΓM M H) hj))).toRingHom) ≫ ιInf p (ΓM M H) hj)
    (hcsnd : c ≫ pullback.snd _ _ =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom
        (R := R p) (A := κ) (B := ↥(chartAlgInf p (ΓM M H) hj)))))

    (comp : Fin 2 → (fibre (Γ := ΓN p M H hpM) (hj := hj) (algebraMap (R p) κ) ⟶ fibre (Γ := ΓM M H) (hj := hj) (algebraMap (R p) κ)))
    (comp_over : ∀ i, comp i ≫ pullback.snd _ _ = pullback.snd _ _)
    (comp_isClosedImmersion : ∀ i, IsClosedImmersion (comp i))
    (comp_pi : comp 0 ≫ fibreMap π (algebraMap (R p) κ) = 𝟙 _) :
    ∃ σ₀ : κ ⊗[R p] ↥(chartAlgInf p (ΓM M H) hj) →ₐ[κ] κ ⊗[R p] ↥(chartAlgInf p (ΓN p M H hpM) hj),
      (∀ z, σ₀ (Algebra.TensorProduct.map (AlgHom.id κ κ) iotaInf z) = z) ∧
      c₀ ≫ comp 0 = Spec.map (CommRingCat.ofHom σ₀.toRingHom) ≫ c := by sorry
