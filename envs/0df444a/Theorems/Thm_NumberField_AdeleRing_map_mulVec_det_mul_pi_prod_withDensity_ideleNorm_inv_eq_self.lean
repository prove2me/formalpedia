-- Prove2me | Theorems.Thm_NumberField_AdeleRing_map_mulVec_det_mul_pi_prod_withDensity_ideleNorm_inv_eq_self
-- name    : NumberField.AdeleRing.map_mulVec_det_mul_pi_prod_withDensity_ideleNorm_inv_eq_self
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.529639+00:00
-- url     : https://prove2.me/theorems/cc15591d-4255-5a73-9313-80601b1861b5
-- title:
--   Adelic measure d²c ‖δ‖⁻¹dδ is GL₂-invariant
-- statement:
--   Let $K$ be a number field, with its adele ring $\mathbb{A} =$ `AdeleRing (𝓞 K) K` equipped with a measurable space structure which is the Borel structure of its topology, and likewise for the unit group $\mathbb{A}^\times$ with the Borel structure of its topology. Let $\mu$ be a measure on $\mathbb{A}$ assumed to be an additive Haar measure, let $\nu$ be a measure on $\mathbb{A}^\times$ assumed to be a Haar measure, and let $h \in \mathrm{GL}_2(\mathbb{A})$. Write $\lambda$ for the product, on $(\mathrm{Fin}\,2 \to \mathbb{A}) \times \mathbb{A}^\times$, of the two-fold product measure $\mu \otimes \mu$ with the measure obtained from $\nu$ by the density $\delta \mapsto \mathrm{ENNReal.ofReal}\,\bigl(\mathrm{ideleNorm}\,K\,\delta\bigr)^{-1}$, where $\mathrm{ideleNorm}\,K\,\delta$ is the real number obtained from the distributive Haar character $\mathrm{distribHaarChar}(\mathbb{A})(\delta)$, i.e. the module of multiplication by $\delta$ on the additive group $\mathbb{A}$. The assertion is that the pushforward of $\lambda$ along the map $(c,\delta) \mapsto \bigl(h \cdot c,\ (\det h)\,\delta\bigr)$, with $h \cdot c$ the matrix–vector product `mulVec` of the underlying matrix of $h$ with $c$ and $\det h \in \mathbb{A}^\times$ the determinant of $h$ as a unit, is again $\lambda$.
--
--   This is the invariance, under the action $(c,\delta) \mapsto (hc, \det(h)\delta)$ of $\mathrm{GL}_2(\mathbb{A}_K)$, of the measure $d^2c \otimes \lVert\delta\rVert^{-1} d^\times\delta$ on $\mathbb{A}_K^2 \times \mathbb{A}_K^\times$, the two factors $\lVert \det h\rVert^{\mp 1}$ cancelling. It is the measure-theoretic input for the computation of Whittaker-type adelic integrals over $\mathrm{GL}_2$ in terms of integrals against $\lVert\delta\rVert^{-1}$, used in the treatment of global zeta integrals for automorphic forms on $\mathrm{GL}_2$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_AdeleRing_map_mulVec_det_mul_pi_prod_withDensity_ideleNorm_inv_eq_self.lean

import Definitions.Def_NumberField_TateGlobalZeta

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain
open scoped ENNReal

theorem NumberField.AdeleRing.map_mulVec_det_mul_pi_prod_withDensity_ideleNorm_inv_eq_self
    (K : Type) [Field K] [NumberField K]
    [MeasurableSpace (AdeleRing (𝓞 K) K)] [BorelSpace (AdeleRing (𝓞 K) K)]
    [MeasurableSpace (AdeleRing (𝓞 K) K)ˣ] [BorelSpace (AdeleRing (𝓞 K) K)ˣ]
    (μ : Measure (AdeleRing (𝓞 K) K)) (hμ : μ.IsAddHaarMeasure)
    (ν : Measure (AdeleRing (𝓞 K) K)ˣ) (hν : ν.IsHaarMeasure)
    (h : GL (Fin 2) (AdeleRing (𝓞 K) K)) :
    Measure.map (fun p : (Fin 2 → AdeleRing (𝓞 K) K) × (AdeleRing (𝓞 K) K)ˣ =>
        ((h : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)).mulVec p.1, Matrix.GeneralLinearGroup.det h * p.2))
      ((Measure.pi fun _ : Fin 2 => μ).prod
        (ν.withDensity fun δ => ENNReal.ofReal (NumberField.TateGlobal.ideleNorm K δ)⁻¹)) =
    (Measure.pi fun _ : Fin 2 => μ).prod
      (ν.withDensity fun δ => ENNReal.ofReal (NumberField.TateGlobal.ideleNorm K δ)⁻¹) := by sorry
