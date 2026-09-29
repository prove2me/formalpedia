-- Prove2me | Theorems.Thm_NumberField_Idele_apply_eq_apply_partAt_mul_prod_apply_det_heckeGen_zpow_ord_of_mem_unitIdelesOutside
-- name    : NumberField.Idele.apply_eq_apply_partAt_mul_prod_apply_det_heckeGen_zpow_ord_of_mem_unitIdelesOutside
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.923973+00:00
-- url     : https://prove2.me/theorems/c8e7b8ef-c025-57d7-a9ef-c4a2528c8e8c
-- title:
--   Unramified idele character: S-part times uniformiser powers at T
-- statement:
--   Let $K$ be a number field, and let $\xi$ be a monoid homomorphism from the full subgroup $\top$ of the idele group $(\mathbb{A}_K)^\times$ to $\mathbb{C}^\times$ such that the associated $\mathbb{C}$-valued function $z \mapsto \xi(z)$ is continuous on $(\mathbb{A}_K)^\times$. Let $S$ and $T$ be finite sets of finite places of $K$ (height-one primes of $\mathcal{O}_K$) with $T$ disjoint from $S$, and assume $\xi$ is unramified outside $S$ in the following sense: for every $v \notin S$ and every unit $t$ of the completion $K_v$ with $v(t) = 1$, the value of $\xi$ at the idele `Units.map (finIncl (𝓞 K) K) (localUnit (𝓞 K) K v t)` — the idele whose finite component is $t$ at $v$ and $1$ at all other finite places, and whose infinite component is $1$ — equals $1$. Let $z$ be an idele lying in [`NumberField.AdeleRing.unitIdelesOutside (𝓞 K) K ↑(S ∪ T)`](def/IsDedekindDomain_FiniteUnitIdelesOutside.html#L51), i.e. such that at every finite place $v \notin S \cup T$ both the $v$-component of $z$ and the $v$-component of $z^{-1}$ lie in the valuation ring $\mathcal{O}_v$. Then $$\xi(z) = \xi\bigl(\mathrm{partAt}_S(z)\bigr) \cdot \prod_{v \in T} \xi\bigl(\det \mathrm{heckeGen}_v\bigr)^{\mathrm{ord}_v(z)},$$ where $\mathrm{partAt}_S(z)$ is the idele obtained from $z$ by keeping its infinite component and applying the multiplicative truncation `truncFin K S` to its finite component, $\mathrm{heckeGen}_v$ is the element of $\mathrm{GL}_2(\mathbb{A}_K)$ built by `diagOne` from the idele with a uniformiser of $v$ at $v$ and $1$ elsewhere, and $\mathrm{ord}_v(z) = -\log v(z_v)$ is the valuation exponent of the $v$-component of $z$.
--
--   This is the standard splitting of a continuous idele quasi-character unramified outside $S$: on ideles that are units away from $S \cup T$, the character is determined by its value on the part at $S$ together with its values on the uniformiser ideles at the places of $T$, raised to the local valuations. It is used to separate variables before the product-measure decomposition of idelic integrals over the valuation shells at $T$, and is cited in the analysis of orbital and class sums for automorphic forms and in the construction of the exponent map on idele characters.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_Idele_apply_eq_apply_partAt_mul_prod_apply_det_heckeGen_zpow_ord_of_mem_unitIdelesOutside.lean

import Definitions.Def_NumberField_IdeleProductMeasure

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel IsDedekindDomain

open scoped Classical in

theorem NumberField.Idele.apply_eq_apply_partAt_mul_prod_apply_det_heckeGen_zpow_ord_of_mem_unitIdelesOutside
    (K : Type) [Field K] [NumberField K] [DecidableEq (HeightOneSpectrum (𝓞 K))]
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (S T : Finset (HeightOneSpectrum (𝓞 K))) (hTS : Disjoint T S)
    (hur : ∀ v ∉ S, ∀ t : (v.adicCompletion K)ˣ, Valued.v (t : v.adicCompletion K) = 1 →
      ξ ⟨Units.map (finIncl (𝓞 K) K) (localUnit (𝓞 K) K v t), Subgroup.mem_top _⟩ = 1)
    (z : (AdeleRing (𝓞 K) K)ˣ)
    (hz : z ∈ NumberField.AdeleRing.unitIdelesOutside (𝓞 K) K (↑(S ∪ T) : Set (HeightOneSpectrum (𝓞 K)))) :
    ξ ⟨z, Subgroup.mem_top z⟩ =
      ξ ⟨NumberField.Idele.partAt K S z, Subgroup.mem_top _⟩ *
        ∏ v ∈ T, ξ ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 K) K v), Subgroup.mem_top _⟩ ^
          NumberField.Idele.ord K v z := by sorry
