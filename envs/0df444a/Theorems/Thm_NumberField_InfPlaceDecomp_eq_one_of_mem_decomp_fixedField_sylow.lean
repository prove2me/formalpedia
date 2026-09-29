-- Prove2me | Theorems.Thm_NumberField_InfPlaceDecomp_eq_one_of_mem_decomp_fixedField_sylow
-- name    : NumberField.InfPlaceDecomp.eq_one_of_mem_decomp_fixedField_sylow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.923973+00:00
-- url     : https://prove2.me/theorems/aaf944bb-08c0-5eb5-83a6-1717e507d077
-- title:
--   Trivial decomposition at infinity over a Sylow fixed field
-- statement:
--   Let $E$ and $F$ be number fields with $F$ an $E$-algebra and $F/E$ Galois, let $p$ be a prime and let $P$ be a Sylow $p$-subgroup of $\mathrm{Gal}(F/E) = F \simeq_{\mathrm{alg}[E]} F$. Assume the following hypothesis, which is required only in the case $p = 2$: if $p = 2$, then for every infinite place $v$ of $F$ and every $g \in \mathrm{Gal}(F/E)$ belonging to the decomposition group of $v$ over $E$ — that is, to the stabiliser of $v$ under the natural action of $\mathrm{Gal}(F/E)$ on the infinite places of $F$ — one has $g = 1$. Then, for every infinite place $v$ of $F$ and every $g$ in the Galois group $\mathrm{Gal}(F/F^{P})$ of $F$ over the fixed field $F^{P}$ of $P$ inside $F$, if $g$ lies in the decomposition group of $v$ over $F^{P}$, i.e. $g$ stabilises $v$, then $g = 1$. Equivalently: all infinite places of $F$ have trivial decomposition group over $F^{P}$, under the stated hypothesis at $p = 2$.
--
--   This records that passing to the fixed field of a Sylow $p$-subgroup preserves (indeed forces) triviality of the decomposition groups at the archimedean places: for odd $p$ this is automatic, since such a decomposition group has order $1$ or $2$ while $\mathrm{Gal}(F/F^{P})$ is a $p$-group, and for $p = 2$ it is inherited from the assumed triviality over the base. It serves as a bookkeeping step in a Sylow descent argument, being used by [`M4aHerbrand.map_pi_eq_zero_iff_finsum_eq_zero_of_pow_smul_eq_zero`](thm.html#M4aHerbrand.map_pi_eq_zero_iff_finsum_eq_zero_of_pow_smul_eq_zero) to pass from $p$-group layers that are unramified at infinity to an arbitrary finite Galois layer.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_InfPlaceDecomp_eq_one_of_mem_decomp_fixedField_sylow.lean

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

theorem NumberField.InfPlaceDecomp.eq_one_of_mem_decomp_fixedField_sylow
    (E F : Type) [Field E] [NumberField E] [Field F] [NumberField F] [Algebra E F] [IsGalois E F]
    (p : ℕ) [Fact p.Prime] (P : Sylow p (F ≃ₐ[E] F))
    (hinf2 : p = 2 → ∀ (v : InfinitePlace F) (g : F ≃ₐ[E] F), g ∈ NumberField.InfPlaceDecomp.decomp E F v → g = 1)
    (v : InfinitePlace F) (g : (F ≃ₐ[↥(IntermediateField.fixedField (P : Subgroup (F ≃ₐ[E] F)))] F)) (hg : g ∈ NumberField.InfPlaceDecomp.decomp ↥(IntermediateField.fixedField (P : Subgroup (F ≃ₐ[E] F))) F v) : g = 1 := by sorry
