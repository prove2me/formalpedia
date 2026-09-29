-- Prove2me | Theorems.Thm_NumberField_Idele_integral_mul_indicator_unitIdelesOutside_mul_prod_translate_eq_mul_integral_mul_prod_tsum
-- name    : NumberField.Idele.integral_mul_indicator_unitIdelesOutside_mul_prod_translate_eq_mul_integral_mul_prod_tsum
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.923973+00:00
-- url     : https://prove2.me/theorems/757462af-f7a4-5ec7-9962-757b148f34be
-- title:
--   Unfolding a translated idele integral off S∪ T
-- statement:
--   Let $K$ be a number field with ring of integers $\mathcal O_K$, let the unit group $(\mathbb A_K)^\times$ of the adele ring carry its Borel measurable structure, and let $\nu$ be a Haar measure on it. Let $\xi$ be a homomorphism from the full subgroup $\top \le (\mathbb A_K)^\times$ to $\mathbb C^\times$ such that $z \mapsto \xi(z) \in \mathbb C$ is continuous, $\xi$ is trivial on the image of $K^\times$ under the principal-idele map, and, for every finite place $v \notin S$ and every local unit $t \in (K_v)^\times$ with $|t| = 1$, $\xi$ kills the idele that is $t$ at $v$ and $1$ elsewhere (`localUnit` followed by `finIncl`). Let $S, T$ be disjoint finite sets of finite places and let `PZ` be product-measure data for $S$ and $\nu$ — a constant $c > 0$, a measure $\nu_S$, a projection homomorphism, an order function, and the decomposition, Tonelli and measurability axioms of [`UnramifiedWhittaker.ProductMeasureData`](def/UnramifiedWhittaker_ZetaIntegrand.html#L20) — whose order function is $v, a \mapsto -\log |a_v|$ and whose projection is truncation of the finite part to $S$. Let $d \in K^\times$, let $\Phi$ be such that $\xi \cdot \Phi$ is $\nu_S$-integrable, and for each $v \in T$ let $\varphi_v : \mathbb Z \to \mathbb C$ satisfy $\sum_e \|\xi(\det \mathrm{heckeGen}_v)^e \varphi_v(e)\| < \infty$. Then the $\nu$-integral over $z$ of $\xi(z)$ times the value at $zd$ of the function supported on the ideles that are units (with unit inverse) at all places outside $S \cup T$ and given there by $\Phi$ of the $S$-truncation times $\prod_{v \in T} \varphi_v(\mathrm{ord}_v)$ equals $c \cdot \bigl(\int \xi \Phi \, d\nu_S\bigr) \cdot \prod_{v \in T} \sum_{e \in \mathbb Z} \xi(\det \mathrm{heckeGen}_v)^e \varphi_v(e)$.
--
--   This is the measure-theoretic unfolding step for an idele-class character integral: a test function built from an $S$-part and finitely many Hecke shells at $T$, translated by a principal idele, integrates to the $S$-part integral times a product of local shell series. It feeds the computation of orbital and zeta integrals attached to Hecke operators, being cited by [`AutomorphicForm.integral_mul_orbital_centralScalar_eq_mul_ideleNorm_mul_prod_tsum_mul_integral_of_isUnitFactorization_of_integrable`](thm.html#AutomorphicForm.integral_mul_orbital_centralScalar_eq_mul_ideleNorm_mul_prod_tsum_mul_integral_of_isUnitFactorization_of_integrable) and by [`NumberField.Idele.integral_mul_prod_mul_finprod_mul_apply_translate_eq_mul_ideleNorm_partAt_mul_prod_tsum_mul_integral`](thm.html#NumberField.Idele.integral_mul_prod_mul_finprod_mul_apply_translate_eq_mul_ideleNorm_partAt_mul_prod_tsum_mul_integral).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_Idele_integral_mul_indicator_unitIdelesOutside_mul_prod_translate_eq_mul_integral_mul_prod_tsum.lean

import Definitions.Def_NumberField_IdeleProductMeasure

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel IsDedekindDomain

open scoped Classical in

theorem NumberField.Idele.integral_mul_indicator_unitIdelesOutside_mul_prod_translate_eq_mul_integral_mul_prod_tsum
    (K : Type) [Field K] [NumberField K] [DecidableEq (HeightOneSpectrum (𝓞 K))]
    [MeasurableSpace (AdeleRing (𝓞 K) K)ˣ] [BorelSpace (AdeleRing (𝓞 K) K)ˣ]
    (νZK : Measure (AdeleRing (𝓞 K) K)ˣ) [νZK.IsHaarMeasure]
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (hξt : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      z ∈ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range →
        ξ ⟨z, Subgroup.mem_top z⟩ = 1)
    (S T : Finset (HeightOneSpectrum (𝓞 K))) (hTS : Disjoint T S)
    (hur : ∀ v ∉ S, ∀ t : (v.adicCompletion K)ˣ, Valued.v (t : v.adicCompletion K) = 1 →
      ξ ⟨Units.map (finIncl (𝓞 K) K) (localUnit (𝓞 K) K v t), Subgroup.mem_top _⟩ = 1)
    (PZ : UnramifiedWhittaker.ProductMeasureData S νZK)
    (hPo : PZ.ord = NumberField.Idele.ord K) (hPp : PZ.projS = NumberField.Idele.partAt K S)
    (d : Kˣ)
    (Φ : (AdeleRing (𝓞 K) K)ˣ → ℂ)
    (hΦ : Integrable (fun zS : (AdeleRing (𝓞 K) K)ˣ => ((ξ ⟨zS, Subgroup.mem_top zS⟩ : ℂˣ) : ℂ) * Φ zS) PZ.νS)
    (φ : HeightOneSpectrum (𝓞 K) → ℤ → ℂ)
    (hφ : ∀ v ∈ T, Summable fun e : ℤ =>
      ‖((ξ ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 K) K v), Subgroup.mem_top _⟩ : ℂˣ) : ℂ) ^ e * φ v e‖) :
    ∫ z : (AdeleRing (𝓞 K) K)ˣ, ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
        (NumberField.AdeleRing.unitIdelesOutside (𝓞 K) K (↑(S ∪ T) : Set (HeightOneSpectrum (𝓞 K))) :
            Set (AdeleRing (𝓞 K) K)ˣ).indicator
          (fun w => Φ (NumberField.Idele.partAt K S w) * ∏ v ∈ T, φ v (NumberField.Idele.ord K v w))
          (z * Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) d) ∂νZK =
      (PZ.c : ℂ) * (∫ zS : (AdeleRing (𝓞 K) K)ˣ, ((ξ ⟨zS, Subgroup.mem_top zS⟩ : ℂˣ) : ℂ) * Φ zS ∂PZ.νS) *
        ∏ v ∈ T, ∑' e : ℤ,
          ((ξ ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 K) K v), Subgroup.mem_top _⟩ : ℂˣ) : ℂ) ^ e * φ v e := by sorry
