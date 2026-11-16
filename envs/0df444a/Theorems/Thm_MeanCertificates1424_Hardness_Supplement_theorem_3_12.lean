-- Prove2me | Theorems.Thm_MeanCertificates1424_Hardness_Supplement_theorem_3_12
-- name    : MeanCertificates1424.Hardness.Supplement.theorem_3_12
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T09:00:05.476054+00:00
-- url     : https://prove2.me/theorems/54ff9ae1-f791-4533-903f-04c5e4b47e68
-- title:
--   Theorem 3.12 — W[1]-hardness in the honest quota
-- statement:
--   Upper-Mean, parameterized by the honest quota $h=n-b$, is W[1]-hard on connected split graphs with $L=1$, $\epsilon=0$, no audits, uniform weights, integer reports and $b<n$.
--
--   Together with Theorem 3.5, exact certification is hard both when few and when many reports are corrupted.
--
--   Differences from the source:
--   - encoding: W[1]-hard → fpt many-one reducible from p-Clique with the new parameter bounded by a computable function of k; reason: standard W[1]-completeness of p-Clique; the brief prescribes this equivalence
--   - reading: Upper-Mean is hard on a restricted class → every NP language (resp. p-Clique) reduces to the restricted language by a reduction whose outputs always lie in the class; reason: hardness of a problem restricted to a class means reductions into that class
-- source:
--   chaomeng chen, Junhao Dong, STOC 2027 submission #1424 (October 2026), Theorem 3.12, printed p.12 (PDF p.14)

import Mathlib
import Definitions.Def_MeanCertificates1424_Hardness_Supplement_Complexity

set_option autoImplicit false

open MeanCertificates1424.Hardness

namespace MeanCertificates1424.Hardness.Supplement

/-- Theorem 3.12, printed p.12 / PDF p.14. Upper-Mean parameterized by the honest quota
`h = n − b` is W[1]-hard on connected split graphs with `L = 1`, `ε = 0`, no audits, uniform
weights and integer reports. -/
theorem theorem_3_12 : W1HardOn (UMLang IntSplit) umHonest (UMOut IntSplit) := by sorry

end MeanCertificates1424.Hardness.Supplement
