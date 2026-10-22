-- Prove2me | Theorems.Thm_HardyCapset20261020_Cert_certificate_checker_sound
-- name    : HardyCapset20261020.Cert.certificate_checker_sound
-- status  : Proved
-- author  : @Somehow
-- created : 2026-10-20T15:30:44.626652+00:00
-- url     : https://prove2.me/theorems/65a1a092-64ed-4835-9e31-5012ce10984c
-- title:
--   Soundness of the finite full-space completion certificate checker
-- statement:
--   For any concrete certificate whose finite checks all hold, every cap containing the exact baseline outside the encoded affine hyperplane has at most 512 points. The checks validate every ambient point against either a candidate witness or a pair of fixed blockers, the geometric conditions of every forbidden pair and triple, the capacity inequality for every local Boolean selection, a nonnegative integer weighted cover of every candidate variable, and a strict total-cost upper bound. The denominator is positive. The conclusion quantifies over arbitrary caps and permits added points anywhere in the ambient space.
-- source:
--   Private source: 八维 cap 的超平面补点定理, 2026-10-13, sections 2–5. The exact baseline is the previously uploaded HardyCapsetModel20261020. This is a conditional fixed-core theorem for that baseline.

import Definitions.Def_HardyCapsetCertificateModel20261020
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.NormNum
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

namespace HardyCapset20261020.Cert
theorem certificate_checker_sound (c : Certificate) (hc : Check c) :
    CompletionBound (decode c.normal) c.level := by sorry
end HardyCapset20261020.Cert
