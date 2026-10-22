-- Prove2me | Theorems.Thm_HardyCapset20261020_Cert_fast_baseline_lookup
-- name    : HardyCapset20261020.Cert.fast_baseline_lookup
-- status  : Proved
-- author  : @Somehow
-- created : 2026-10-20T17:06:31.773256+00:00
-- url     : https://prove2.me/theorems/872b5bbf-d52b-42bc-81f4-d5c26dec47ac
-- title:
--   Exact equality of packed and original baseline lookups
-- statement:
--   For every natural index, the packed lookup equals the corresponding entry of the exact original baseline list, including zero default for all out-of-range indices. Every one of the 512 entries is verified in Lean.
-- source:
--   Private source: 八维 cap 的超平面补点定理, 2026-10-13, sections 2–5. The exact baseline is the previously uploaded HardyCapsetModel20261020. This is a conditional fixed-core theorem for that baseline.

import Definitions.Def_HardyCapsetFastBaselineLookup20261021

namespace HardyCapset20261020.Cert
theorem fast_baseline_lookup (a : Nat) : baseAt a = fastBaseAt a := by sorry
end HardyCapset20261020.Cert
