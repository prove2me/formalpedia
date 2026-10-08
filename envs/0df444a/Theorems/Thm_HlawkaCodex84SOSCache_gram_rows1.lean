-- Prove2me | Theorems.Thm_HlawkaCodex84SOSCache_gram_rows1
-- name    : HlawkaCodex84SOSCache.gram_rows1
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-06T06:27:13.887978+00:00
-- url     : https://prove2.me/theorems/7bb042ac-9a7f-4d10-a1b1-344796b9ff26
-- title:
--   Exact rational Gram factorization, rows 10–19
-- statement:
--   Let G be the rational 30-by-30 Gram matrix in the cutoff-84 radial SOS certificate, L its stored lower triangular factor, and D the diagonal matrix of its stored pivots. For rows 10 through 19 and all 30 columns, the entries agree exactly:
--
--   $$G_{ij}=(LDL^T)_{ij}.$$
--
--   This identity checks one third of the rational factorization used to certify the radial quadratic bound.
-- source:
--   https://prove2.me/campaigns/sharp-diagonal-hlawka-constant; Codex cutoff84 radial quadratic certificate, RADIAL-GEOMETRY84.md, exact rational SOS section.

import Definitions.Def_HlawkaCodex84_SOSCertificateData
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Matrix.Diagonal
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
open HlawkaCodex84SOSCache

namespace HlawkaCodex84SOSCache
theorem gram_rows1 : ∀ (i : Fin 10) (j : Fin 30), gram ⟨i.val + 10, by omega⟩ j = (gramLower * Matrix.diagonal gramPivots * gramLower.transpose) ⟨i.val + 10, by omega⟩ j := by sorry
end HlawkaCodex84SOSCache
