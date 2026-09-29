-- Prove2me | Theorems.Thm_HorizontalPadicL_SeedCyclotomicGaloisCharacterDataV2_exists_fullOrder_value_v2
-- name    : HorizontalPadicL.SeedCyclotomicGaloisCharacterDataV2.exists_fullOrder_value_v2
-- status  : Proved
-- author  : @davidloeffler
-- created : 2026-09-25T11:46:25.788657+00:00
-- url     : https://prove2.me/theorems/9606b52a-0137-48ed-adb7-fbb513d1c658
-- title:
--   A faithful seed Galois realization contains a full-order character value
-- statement:
--   A faithful seed/cyclotomic Galois realization contains a unit residue class a such that eta(a) has the full order of eta.
-- source:
--   Immediate from the distinguished full-order seed generator and the exact description of the seed-character image.

import Definitions.Def_KN_SeedCyclotomicGaloisCharactersV3B

set_option autoImplicit false
noncomputable section

namespace HorizontalPadicL

/-- A faithful seed/cyclotomic Galois realization supplies a residue class on
which the seed Dirichlet character has its full order. -/
theorem SeedCyclotomicGaloisCharacterDataV2.exists_fullOrder_value_v2
    {N p m : ℕ} [Fact p.Prime]
    (η : DirichletCharacterWithLevel)
    (C : SeedCyclotomicGaloisCharacterDataV2 N p m η) :
    ∃ a : (ZMod η.1.1)ˣ,
      orderOf (η.2 (a : ZMod η.1.1)) = orderOf η.2 := by sorry

end HorizontalPadicL
