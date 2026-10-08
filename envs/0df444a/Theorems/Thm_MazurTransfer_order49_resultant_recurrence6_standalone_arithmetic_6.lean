-- Prove2me | Theorems.Thm_MazurTransfer_order49_resultant_recurrence6_standalone_arithmetic_6
-- name    : MazurTransfer.order49_resultant_recurrence6_standalone_arithmetic_6
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-06T21:04:53.13485+00:00
-- url     : https://prove2.me/theorems/b4bb6f89-5521-4568-9a4e-b45354f07ba9
-- title:
--   Order-49 sixth recurrence: Constant-linear and leading-quadratic product
-- statement:
--   Work in the rational polynomial ring $\mathbb Q[D]$. Let $A_0,A_1,A_2,B_0,B_1,e$ be the fixed normalized coefficients, and $S_A,S_B,P_{02},P_{11},I,T_1,T_2,T_3$ the exact intermediate polynomials in the published arithmetic data. Prove the unconditional identity
--
--   $$P_{02}=B_0 A_2.$$
--
--   This is one of the nine exact arithmetic steps proving $B_1^2A_0=B_0(B_1A_1-B_0A_2)-A_2^2e$, used in the sixth pseudo-division recurrence of the full order-49 exclusion. No scalar identity or torsion hypothesis is assumed.
-- source:
--   User MazurTheorem WIP 54d43d8dda8a6fcf069cc02a815f850d762c5c0c; exact original theorem MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder7Coefficient0TimesRemainder6Coefficient2_eq and complete Lean AST signature range retained. Proof assembled from kernel dependencies and complete original AST commands. Custom rational syntax is expanded at AST-owned term ranges, each replacement separately verified by rfl. All original mathematical types, values, coefficients and Apache-2.0 headers retained. Named consumer: normalizedScalarResidual6. Standalone publication boundary: all exact original data values are kernel-compared with namespace-separated rational polynomial definitions. Original proof body selected at complete AST boundaries and wrapped in the same namespace; all resolved statement references retargeted at AST-owned byte positions. No mathematical values, binders, hypotheses or conclusions are weakened. Named consumer: the exact original normalized scalar platform theorem through its checked data equivalence bridge.

import Definitions.Def_MazurTransfer_Order49Recurrence6StandaloneNormalizedData
import Definitions.Def_MazurTransfer_Order49Recurrence6StandaloneArithmeticData0
open Polynomial
open MazurTransfer.Order49Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate

theorem MazurTransfer.order49_resultant_recurrence6_standalone_arithmetic_6 :
MazurTransfer.Order49Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder7Coefficient0Normalized * MazurTransfer.Order49Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder6Coefficient2Normalized =
      MazurTransfer.Order49Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder7Coefficient0TimesRemainder6Coefficient2 := by sorry
