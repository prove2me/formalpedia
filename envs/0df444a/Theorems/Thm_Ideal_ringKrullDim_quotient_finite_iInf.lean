-- Prove2me | Theorems.Thm_Ideal_ringKrullDim_quotient_finite_iInf
-- name    : Ideal.ringKrullDim_quotient_finite_iInf
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-27T07:02:00.288033+00:00
-- url     : https://prove2.me/theorems/37efa015-5593-4011-a4d9-7d86c53de836
-- title:
--   Krull dimension of a quotient by a finite intersection
-- statement:
--   For a commutative ring $R$ and any finite family of ideals $(I_i)$, including the empty family,
--   $$\dim(R/\bigcap_i I_i)=\sup_i\dim(R/I_i).$$
--   Dimensions are actual prime-chain Krull dimensions, with the zero ring assigned bottom and unbounded dimensions assigned infinity. No Noetherian or field hypothesis is required.
-- source:
--   Direct prime-chain proof from the definition of Krull dimension and the finite-intersection property of prime ideals. General support lemma for Philippon §3, https://www.numdam.org/articles/10.24033/bsmf.2060/ .

import Mathlib
set_option autoImplicit false

theorem Ideal.ringKrullDim_quotient_finite_iInf
    {R ι : Type*} [CommRing R] [Finite ι] (A : ι → Ideal R) :
    ringKrullDim (R ⧸ ⨅ i, A i) = ⨆ i, ringKrullDim (R ⧸ A i) := by sorry
