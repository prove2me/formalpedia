-- Prove2me | Theorems.Thm_ModularCurve_linearIndependent_coeffMap
-- name    : ModularCurve.linearIndependent_coeffMap
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.34379+00:00
-- url     : https://prove2.me/theorems/5523be27-dacc-5e49-9ddd-122fcc9837e7
-- title:
--   Coefficientwise base change preserves linear independence of Laurent series
-- statement:
--   Let $k_0$ and $k$ be fields and let $\sigma \colon k_0 \to k$ be a ring homomorphism. Let $n$ be a natural number and let $v \colon \mathrm{Fin}\,n \to k_0((q))$ be a family of Laurent series over $k_0$ (Hahn series over $k_0$ with value group $\mathbb{Z}$), assumed linearly independent over $k_0$. Here `coeffMap` $\sigma$ denotes the ring homomorphism $k_0((q)) \to k((q))$ obtained by applying $\sigma$ to each coefficient, i.e. sending a series to its image under `HahnSeries.map` $\sigma$. The conclusion is that the family $i \mapsto$ `coeffMap` $\sigma\,(v\,i)$ of Laurent series over $k$ is linearly independent over $k$. No further hypothesis on $\sigma$ is imposed; injectivity is automatic, $\sigma$ being a homomorphism of fields.
--
--   This is the standard fact that coefficientwise extension of scalars along a field homomorphism preserves linear independence of $q$-expansions, in the form needed when passing from a base field to an extension or to a residue field. It is used in the construction of place specialisations of prolongation tuples and in the characteristic-$p$ statement [`ModularCurve.exists_mem_zmod_coeffMap_eq_of_coeff_pow_char_eq`](thm.html#ModularCurve.exists_mem_zmod_coeffMap_eq_of_coeff_pow_char_eq).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_linearIndependent_coeffMap.lean

import Mathlib
import Definitions.Def_ModularCurve_LaurentCoeff

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open ModularCurve

theorem ModularCurve.linearIndependent_coeffMap {k₀ k : Type*} [Field k₀] [Field k] (σ : k₀ →+* k)
    {n : ℕ} {v : Fin n → LaurentSeries k₀} (hv : LinearIndependent k₀ v) :
    LinearIndependent k (fun i => coeffMap σ (v i)) := by sorry
