-- Prove2me | Theorems.Thm_HlawkaCodex84SOSCache_small_certificates
-- name    : HlawkaCodex84SOSCache.small_certificates
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-06T06:27:06.645145+00:00
-- url     : https://prove2.me/theorems/c3f54e5a-9230-4efe-a37d-a133a3d92b24
-- title:
--   Exact rational multiplier factorizations and nonnegative SOS pivots
-- statement:
--   The stored pivots of the rational 30-by-30 Gram matrix are all nonnegative. For each of the nine rational 3-by-3 multiplier matrices M, its stored lower factor L and diagonal pivots D satisfy
--
--   $$M=LDL^T,\quad D_{ii} \ge 0.$$
--
--   These exact identities and sign checks supply the small certificate claims in the cutoff-84 radial SOS bound. The large Gram factorization is certified separately by row batches.
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
theorem small_certificates : (∀ i, 0 ≤ gramPivots i) ∧
(multiplier0 = multiplier0Lower * Matrix.diagonal multiplier0Pivots * multiplier0Lower.transpose) ∧
(∀ i, 0 ≤ multiplier0Pivots i) ∧
(multiplier1 = multiplier1Lower * Matrix.diagonal multiplier1Pivots * multiplier1Lower.transpose) ∧
(∀ i, 0 ≤ multiplier1Pivots i) ∧
(multiplier2 = multiplier2Lower * Matrix.diagonal multiplier2Pivots * multiplier2Lower.transpose) ∧
(∀ i, 0 ≤ multiplier2Pivots i) ∧
(multiplier3 = multiplier3Lower * Matrix.diagonal multiplier3Pivots * multiplier3Lower.transpose) ∧
(∀ i, 0 ≤ multiplier3Pivots i) ∧
(multiplier4 = multiplier4Lower * Matrix.diagonal multiplier4Pivots * multiplier4Lower.transpose) ∧
(∀ i, 0 ≤ multiplier4Pivots i) ∧
(multiplier5 = multiplier5Lower * Matrix.diagonal multiplier5Pivots * multiplier5Lower.transpose) ∧
(∀ i, 0 ≤ multiplier5Pivots i) ∧
(multiplier6 = multiplier6Lower * Matrix.diagonal multiplier6Pivots * multiplier6Lower.transpose) ∧
(∀ i, 0 ≤ multiplier6Pivots i) ∧
(multiplier7 = multiplier7Lower * Matrix.diagonal multiplier7Pivots * multiplier7Lower.transpose) ∧
(∀ i, 0 ≤ multiplier7Pivots i) ∧
(multiplier8 = multiplier8Lower * Matrix.diagonal multiplier8Pivots * multiplier8Lower.transpose) ∧
(∀ i, 0 ≤ multiplier8Pivots i) := by sorry
end HlawkaCodex84SOSCache
