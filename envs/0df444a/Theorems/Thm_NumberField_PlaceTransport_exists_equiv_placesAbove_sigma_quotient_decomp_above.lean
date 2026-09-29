-- Prove2me | Theorems.Thm_NumberField_PlaceTransport_exists_equiv_placesAbove_sigma_quotient_decomp_above
-- name    : NumberField.PlaceTransport.exists_equiv_placesAbove_sigma_quotient_decomp_above
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:57.351487+00:00
-- url     : https://prove2.me/theorems/ea745075-9d77-5dca-ad54-0cb4c5af58f1
-- title:
--   Places above S as a disjoint union of coset spaces
-- statement:
--   Let $E$ and $K$ be number fields with $K$ an algebra over $E$ such that $K/E$ is Galois, write $G = K \simeq_{\mathrm{alg}[E]} K$ for its Galois group, and let $S$ be a finite set of height-one primes of $\mathcal{O}_E$. The assertion is that there exists a bijection $e$ from the set of height-one primes $w$ of $\mathcal{O}_K$ whose contraction `w.under` to $\mathcal{O}_E$ lies in $S$ (this is [`NumberField.SUnits.placesAbove E K S`](def/NumberField_SUnitsModule.html#L19), taken as a subtype) to the sigma type $\Sigma_{v \in S}\, G / D_{w(v)}$, where $w(v) =$ [`NumberField.PlaceAbove.above E K v`](def/NumberField_PlaceAbove.html#L27) is the chosen prime of $\mathcal{O}_K$ above $v$ and $D_{w(v)} =$ [`NumberField.PlaceDecomp.decomp E K (above E K v)`](def/NumberField_PlaceDecompositionAction.html#L82) is the decomposition subgroup over $E$ of the valuation subring of the valuation attached to $w(v)$, with the following equivariance: for every $\sigma \in G$ and all $w, w'$ in `placesAbove E K S`, if $w' = \sigma \bullet w$ as primes of $\mathcal{O}_K$ then $e\,w' = \sigma \bullet e\,w$. Equivariance is thus phrased as an implication about the ambient action on height-one primes of $\mathcal{O}_K$, no action on the subtype being used.
--
--   This is the orbit–stabiliser description of the finite places of $K$ above a finite set $S$ of primes of $E$ as a $G$-set: the places above $S$ decompose as the disjoint union over $v \in S$ of the coset spaces of the decomposition subgroups. It feeds the computation of ranks of invariants of $S$-units modulo $p$, being cited by [`NumberField.LevelArith.finrank_invariants_unitsModP_tensor_add_finrank_invariants_eq`](thm.html#NumberField.LevelArith.finrank_invariants_unitsModP_tensor_add_finrank_invariants_eq).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_PlaceTransport_exists_equiv_placesAbove_sigma_quotient_decomp_above.lean

import Mathlib
import Definitions.Def_GroupCohomology_ContinuousUnramified
import Definitions.Def_DualSelmer_ExtConditions
import Definitions.Def_ExtCitation_KummerBridge
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevel
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevelMap
import Definitions.Def_NumberField_LevelArithmeticModP
import Definitions.Def_NumberField_PlaceTransport

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory MonoidalCategory Module IsDedekindDomain NumberField NumberField.LevelArith
open scoped Classical NumberField.LevelArith NumberField.PlaceTransport

theorem NumberField.PlaceTransport.exists_equiv_placesAbove_sigma_quotient_decomp_above
    (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] [Algebra E K] [IsGalois E K]
    (S : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 E))) :
    ∃ e : ↥(NumberField.SUnits.placesAbove E K S) ≃
        Σ v : S, (K ≃ₐ[E] K) ⧸ NumberField.PlaceDecomp.decomp E K (NumberField.PlaceAbove.above E K v),
      ∀ (σ : K ≃ₐ[E] K) (w w' : ↥(NumberField.SUnits.placesAbove E K S)),
        (w' : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) = σ • (w : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) → e w' = σ • e w := by sorry
