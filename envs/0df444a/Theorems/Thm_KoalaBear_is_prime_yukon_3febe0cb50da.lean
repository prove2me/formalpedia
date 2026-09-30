-- Prove2me | Theorems.Thm_KoalaBear_is_prime_yukon_3febe0cb50da
-- name    : KoalaBear.is_prime_yukon_3febe0cb50da
-- status  : Proved
-- author  : @yukon
-- created : 2026-09-30T04:28:00.099893+00:00
-- url     : https://prove2.me/theorems/88dbe93b-1b14-4e55-b150-1bd893ff7d59
-- title:
--   KoalaBear.is_prime
-- statement:
--   The KoalaBear modulus is prime.
-- source:
--   https://github.com/zksecurity/CompPoly/blob/641694629e4557520a1539b272ec338c9f3044c7/CompPoly/Fields/KoalaBear/Basic.lean
--
--   yukon-proof-operation:d88a12f3-2a69-48e5-84a3-e8d7856b6bd9; Yukon contributor: historical-source-bootstrap
--   [yukon-proof-receipt:eyJ2IjoxLCJtYXJrZXIiOiJ5dWtvbi1wcm9vZi1vcGVyYXRpb246ZDg4YTEyZjMtMmE2OS00OGU1LTg0YTMtZThkNzg1NmI2YmQ5OyBZdWtvbiBjb250cmlidXRvcjogaGlzdG9yaWNhbC1zb3VyY2UtYm9vdHN0cmFwIiwiaGFzaCI6Ijk4ODJlNzI2ODUyM2YzMTZiNmM3OTdjZjczMDNkOWNjMmU2YTE1Y2JmNTI3ZDkxNmNlNmFjZjI4MTU5ZjFhZGMiLCJraW5kIjoicHJvYmxlbSIsInRhcmdldCI6IktvYWxhQmVhci5pc19wcmltZV95dWtvbl8zZmViZTBjYjUwZGEiLCJlbnZpcm9ubWVudCI6eyJ0b29sY2hhaW4iOiJsZWFucHJvdmVyL2xlYW40OnY0LjMzLjEiLCJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCJ9LCJ0YWciOiJiZXR0ZXItY29kZXMtaGlzdG9yeSJ9]

/-
Copyright (c) 2024 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Valerii Huhnin
-/
module



public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import Mathlib.FieldTheory.Finite.Basic


public import Mathlib
public import Definitions.Def_Yukon_b0cfdbaf70ca87129aa06e66
@[expose] public section
/-!
  # KoalaBear Field `2^{31} - 2^{24} + 1`

  This is the field used for lean Ethereum spec.
-/

@[expose] public section

namespace KoalaBear
-- 2130706433
-- #eval fieldSize

/-- The KoalaBear modulus is prime. -/
theorem is_prime_yukon_3febe0cb50da : Nat.Prime fieldSize  := by sorry
end KoalaBear
end
end
