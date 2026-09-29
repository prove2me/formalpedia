-- Prove2me | Theorems.Thm_OPG401_common_allowed_colors
-- name    : OPG401.common_allowed_colors
-- status  : Proved
-- author  : @hao jia
-- created : 2026-09-07T07:13:51.24428+00:00
-- url     : https://prove2.me/theorems/545f2ae3-c6e6-419a-b9d2-ee2211eabe9b
-- title:
--   Exact common-color table in the (20,7) palette
-- statement:
--   For colors $a,b\in\mathbb Z_{20}$, let $A(a)$ and $A(b)$ be the residues that are $(20,7)$-compatible with $a$ and $b$. If $d_{20}(a,b)$ is their shortest cyclic distance, then
--
--   $$
--   |A(a)\cap A(b)|=7-d_{20}(a,b),
--   \qquad
--   A(a)\cap A(b)\ne\varnothing\iff d_{20}(a,b)\le6.
--   $$
--
--   Natural subtraction is used in the cardinality formula. The statement covers all ordered color pairs, including equal and antipodal residues. It is the finite boundary table for preserving a coloring while restoring a degree-two vertex.
-- source:
--   VibeMathing candidate_only local table at repository commit 7928d42a5c57e0c94bbc694b1ee2efc63836ee39, research/artifacts/candidates/opg401-a01-v01-local-audit/proof.md

import Definitions.Def_opg401_circular_coloring

namespace OPG401

/-- The exact local `(20,7)` extension table for two prescribed neighbor
colors, including equal and antipodal colors. -/
theorem common_allowed_colors (a b : Fin 20) :
    ((allowedColors a ∩ allowedColors b).card = 7 - circularDistance a b) ∧
    ((allowedColors a ∩ allowedColors b).Nonempty ↔ circularDistance a b ≤ 6) := by sorry

end OPG401
