-- Prove2me | Theorems.Thm_MazurTransfer_Order13ActualGeometricNineteenTorsionCardinality_actual_nineteenTorsion_finrank_eq_four
-- name    : MazurTransfer.Order13ActualGeometricNineteenTorsionCardinality.actual_nineteenTorsion_finrank_eq_four
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-18T10:33:59.593265+00:00
-- url     : https://prove2.me/theorems/5cd1ba89-382c-4684-ae5b-4d7ad7d87817
-- title:
--   The actual Picard nineteen-torsion has F19 dimension four
-- statement:
--   For every algebraically closed characteristic-zero field K in the original universe, the original F19-module on the nineteen-torsion of the same designated rational Picard has dimension four. The scalar action is exactly the original nineteenTorsionZModModule constructor; no dimension assumption is supplied.
-- source:
--   MazurTheorem Order13ActualGeometricNineteenTorsionCardinality.actual_nineteenTorsion_finrank_eq_four, preserving the original module action and all field hypotheses.

import Definitions.Def_MazurTransfer_Order13ActualNineteenTorsionOriginalZModModuleData20261018
noncomputable section
open MazurTransfer
open Order13ActualNormKernelProductCardinality Order13ActualGeometricNineteenTorsionCardinality
local instance actualTorsionDimensionPrimeFactPublic20261018 : Fact (Nat.Prime 19) := ⟨by decide⟩
attribute [local instance] nineteenTorsionZModModule

theorem MazurTransfer.Order13ActualGeometricNineteenTorsionCardinality.actual_nineteenTorsion_finrank_eq_four (K : Type) [Field K] [CharZero K] [IsAlgClosed K] :
    Module.finrank (ZMod 19) (NineteenTorsion K) = 4 := by sorry
