-- Prove2me | Theorems.Thm_NumberField_PlaceDecomp_finsum_div_natCard_decomp_eq_finrank_smul_finsum
-- name    : NumberField.PlaceDecomp.finsum_div_natCard_decomp_eq_finrank_smul_finsum
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:57.351487+00:00
-- url     : https://prove2.me/theorems/9b229111-3bf6-50dc-9756-baa1ad0c710d
-- title:
--   Degree formula for place sums in ℚ/ℤ
-- statement:
--   Let $E$ and $F$ be number fields with $F$ a Galois extension of $E$, let $E'$ be an intermediate field of $F/E$, and let $n$ be an integer-valued function on the height one primes of $\mathcal{O}_E$. For a height one prime $v$ of $\mathcal{O}_E$ write $\mathrm{above}\,v$ for the chosen height one prime of $\mathcal{O}_F$ lying over $v$ and $\mathrm{decomp}$ for the decomposition subgroup of the corresponding valuation subring inside $F \simeq_{\mathrm{alg}[E]} F$, so that $\mathrm{Nat.card}$ of it is the order of that decomposition group; the same notions are used with $E'$ in place of $E$, the Galois group then being that of $F$ over $E'$. Assume that the family $v \mapsto n_v/\#\mathrm{decomp}(\mathrm{above}\,v)$, viewed in $\mathbb{Q}/\mathbb{Z}$ (Mathlib's `AddCircle (1 : ℚ)`), has finite support. Then the finite-support sum over the height one primes $v'$ of $\mathcal{O}_{E'}$ of the classes of $n_{v'\cap \mathcal{O}_E}/\#\mathrm{decomp}(\mathrm{above}\,v')$, where $v'\cap\mathcal{O}_E$ denotes the prime of $\mathcal{O}_E$ under $v'$, equals $[E':E]$ times the corresponding sum over the height one primes of $\mathcal{O}_E$, the product being the $\mathbb{N}$-action on $\mathbb{Q}/\mathbb{Z}$.
--
--   This is the degree formula for sums of local contributions $n_v/|D_w|$ in $\mathbb{Q}/\mathbb{Z}$: passing from the base field $E$ to an intermediate field $E'$ multiplies the sum by $[E':E]$, because the orders of the decomposition groups relate to ramification indices and inertia degrees through [`NumberField.PlaceDecomp.natCard_decomp_eq_ramificationIdx_mul_inertiaDeg`](thm.html#NumberField.PlaceDecomp.natCard_decomp_eq_ramificationIdx_mul_inertiaDeg). It is a bookkeeping step in the Sylow descent of Tate's reciprocity law from $p$-group layers to an arbitrary finite Galois layer, and is cited by [`M4aHerbrand.exists_invariant_forall_inv_map_eq_finsum_of_forall_localFundamentalClass_of_isPGroup`](thm.html#M4aHerbrand.exists_invariant_forall_inv_map_eq_finsum_of_forall_localFundamentalClass_of_isPGroup) and [`M4aHerbrand.finsum_sylow_eq_zero_iff_finsum_eq_zero_of_pow_smul_eq_zero`](thm.html#M4aHerbrand.finsum_sylow_eq_zero_iff_finsum_eq_zero_of_pow_smul_eq_zero).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_PlaceDecomp_finsum_div_natCard_decomp_eq_finrank_smul_finsum.lean

import Mathlib
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_NumberField_PlaceDecompositionAction
import Definitions.Def_NumberField_ArchimedeanIdeleModule
import Definitions.Def_NumberField_SIdeleModule
import Definitions.Def_NumberField_PlaceAbove
import Definitions.Def_ExtCitation_LocalLevel_FundamentalClass

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
open CategoryTheory NumberField IsDedekindDomain M4aHerbrand
open scoped NumberField.PlaceDecomp

theorem NumberField.PlaceDecomp.finsum_div_natCard_decomp_eq_finrank_smul_finsum
    (E F : Type) [Field E] [NumberField E] [Field F] [NumberField F] [Algebra E F] [IsGalois E F]
    (E' : IntermediateField E F) (n : HeightOneSpectrum (𝓞 E) → ℤ)
    (hfin : (Function.support fun v : HeightOneSpectrum (𝓞 E) =>
      ((((n v : ℚ) / (Nat.card ↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v)) : ℚ) : ℚ) : AddCircle (1 : ℚ)))).Finite) :
    (∑ᶠ v' : HeightOneSpectrum (𝓞 ↥E'),
        ((((n (v'.under (𝓞 E)) : ℚ) / (Nat.card ↥(NumberField.PlaceDecomp.decomp ↥E' F (NumberField.PlaceAbove.above ↥E' F v')) : ℚ) : ℚ) : AddCircle (1 : ℚ)))) =
      Module.finrank E ↥E' •
        (∑ᶠ v : HeightOneSpectrum (𝓞 E),
          ((((n v : ℚ) / (Nat.card ↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v)) : ℚ) : ℚ) : AddCircle (1 : ℚ)))) := by sorry
