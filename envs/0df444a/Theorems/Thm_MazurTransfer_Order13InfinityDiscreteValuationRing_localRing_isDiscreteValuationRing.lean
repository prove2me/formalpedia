-- Prove2me | Theorems.Thm_MazurTransfer_Order13InfinityDiscreteValuationRing_localRing_isDiscreteValuationRing
-- name    : MazurTransfer.Order13InfinityDiscreteValuationRing.localRing_isDiscreteValuationRing
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-17T11:50:25.322609+00:00
-- url     : https://prove2.me/theorems/85e47664-bab8-47b1-9c5f-af0ce0c0230b
-- title:
--   The actual infinity local rings are discrete valuation rings
-- statement:
--   Let $K$ be a field of characteristic zero and let $a^2=1$. The actual reciprocal coordinate algebra localized at the infinity evaluation kernel for $(0,a)$ is a discrete valuation ring: $$A_{\mathfrak m_a}\ \text{is a DVR}.$$ The previously proved principal maximal ideal, noetherian domain structure, and nonzero reciprocal coordinate give the original DVR structure. This supplies exact Pell orders at infinity.
-- source:
--   Original complete retained MazurTheorem proof, Apache-2.0, Vas and contributors. The complete original DVR contract and main proof are retained. The original non-field helper is inlined, using the Proved principal-maximal-ideal theorem and original nonzero-coordinate facts. The main proof only qualifies that helper. Native, strict and complete frontend checks pass; full original and public closed types are kernel-compared. The design boundary and named downstream consumer are explicit in the source and source-authority manifest.

/- Copyright (c) 2026 Vas and contributors. Apache-2.0.
Design boundary: the actual infinity local ring is a DVR in characteristic zero.
Named downstream consumer: exact local Pell orders and the actual principal divisor. -/
import Mathlib
import Definitions.Def_MazurTransfer_Order13InfinityLocalRingDomain
noncomputable section
universe u
open MazurTransfer
open MazurTorsion.XOneThirteenProjectiveCurve
open Order13InfinityLocalParameter Order13InfinityDiscreteValuationRing
variable (K : Type u) [Field K] [CharZero K] (a : K) (ha : a ^ 2 = 1)

theorem MazurTransfer.Order13InfinityDiscreteValuationRing.localRing_isDiscreteValuationRing : IsDiscreteValuationRing (LocalRing K a ha) := by sorry
