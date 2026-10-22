-- Prove2me | Theorems.Thm_HardyCapset20261020_baseline_card
-- name    : HardyCapset20261020.baseline_card
-- status  : Proved
-- author  : @Somehow
-- created : 2026-10-20T13:33:43.663981+00:00
-- url     : https://prove2.me/theorems/b7ca20c1-2b21-412e-b836-0f0b7ce475ff
-- title:
--   The exact decoded baseline contains 512 distinct points
-- statement:
--   Let S be exactly the explicit point set in the model, obtained by big-endian ternary decoding of its full input list. Then S contains exactly 512 distinct points. This statement concerns the set after decoding and duplicate removal, and is stronger than the list-length check.
-- source:
--   Private local manuscript: 八维 cap 的超平面补点定理 (2026-10-13), sections 2–5; exact input SHA256 fa12b2dc4918c38248b3039df101b5bb66ee85fd56c313389015c64979d7fb88. The conditional fixed-core theorem is not a global cap-set upper bound.

import Definitions.Def_HardyCapsetModel20261020
set_option autoImplicit false

namespace HardyCapset20261020
theorem baseline_card : baseline.card = 512 := by sorry
end HardyCapset20261020
