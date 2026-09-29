-- Prove2me | Theorems.Thm_NumberField_Idele_exists_map_ringEquiv_mixedSpace_sPartMeasure_empty_eq_smul_withDensity
-- name    : NumberField.Idele.exists_map_ringEquiv_mixedSpace_sPartMeasure_empty_eq_smul_withDensity
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.923973+00:00
-- url     : https://prove2.me/theorems/0103a8e9-daeb-51c6-9a33-19f7889b245e
-- title:
--   Archimedean idelic measure as Lebesgue measure with Haar density
-- statement:
--   Let $K$ be a number field. The idele group $(\mathbb{A}_K^\times) = (\mathrm{AdeleRing}(\mathcal{O}_K,K))^\times$ is given its Borel $\sigma$-algebra, and [`NumberField.Idele.idelicHaar K`](def/NumberField_IdeleProductMeasure.html#L391) denotes the associated Haar measure `Measure.haar`. Put $\nu_\emptyset :=$ [`NumberField.Idele.sPartMeasure K ∅`](def/NumberField_IdeleProductMeasure.html#L458), the push-forward along the group endomorphism `partAt K ∅` (the map induced on unit groups by the ring homomorphism `partAtAdele K ∅`) of this Haar measure restricted to the subgroup [`NumberField.AdeleRing.unitIdelesOutside (𝓞 K) K ∅`](def/IsDedekindDomain_FiniteUnitIdelesOutside.html#L51) of those unit ideles $\delta$ whose finite component satisfies, at every finite place $v$ of $K$, that both $\delta_v$ and $(\delta^{-1})_v$ lie in the valuation ring $\mathcal{O}_v$. The assertion is that there exists a constant $C \in [0,\infty]$ with $C \neq 0$ and $C \neq \infty$ such that the push-forward of $\nu_\emptyset$ along the map sending a unit idele $a$ to the image under the ring isomorphism `InfiniteAdeleRing.ringEquiv_mixedSpace K` of the infinite component of $a$ equals $C$ times the measure on the mixed space $\prod_{w \text{ real}} \mathbb{R} \times \prod_{w \text{ complex}} \mathbb{C}$ obtained from Lebesgue measure `volume` by the density $z \mapsto \bigl(\mathrm{ofReal}\,\bigl((\prod_{w\text{ real}} |z_w|) \cdot \prod_{w \text{ complex}} \|z_w\|^2\bigr)\bigr)^{-1}$, the inverse being taken in $[0,\infty]$, so that the density is $+\infty$ where the product vanishes.
--
--   This identifies the archimedean part of the multiplicative (idelic) Haar measure, up to a positive finite constant, with Tate's measure $\prod_w d x_w/|x_w|_w$ on $\prod_w K_w^\times$ written on the mixed space $\mathbb{R}^{r_1} \times \mathbb{C}^{r_2}$. It is used in the global computations of Tate-type integrals: in the non-vanishing of an additive-character integral against $\nu_\emptyset$, in the comparison of the measure of a fundamental domain for the unit ideles with the regulator, and in the construction of cusp forms in the converse direction of Langlands–Tunnell.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_Idele_exists_map_ringEquiv_mixedSpace_sPartMeasure_empty_eq_smul_withDensity.lean

import Definitions.Def_NumberField_IdeleProductMeasure
import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Classical

open MeasureTheory NumberField IsDedekindDomain
open scoped ENNReal

attribute [local instance] NumberField.Idele.ideleBorel NumberField.Idele.borelSpace_ideleBorel

theorem NumberField.Idele.exists_map_ringEquiv_mixedSpace_sPartMeasure_empty_eq_smul_withDensity
    (K : Type) [Field K] [NumberField K] :
    ∃ C : ℝ≥0∞, C ≠ 0 ∧ C ≠ ⊤ ∧
      Measure.map (fun a : (AdeleRing (𝓞 K) K)ˣ =>
          InfiniteAdeleRing.ringEquiv_mixedSpace K ((a : AdeleRing (𝓞 K) K)).1)
        (NumberField.Idele.sPartMeasure K ∅) =
      C • (volume : Measure (mixedEmbedding.mixedSpace K)).withDensity
        (fun z => (ENNReal.ofReal ((∏ w, |z.1 w|) * ∏ w, ‖z.2 w‖ ^ 2))⁻¹) := by sorry
