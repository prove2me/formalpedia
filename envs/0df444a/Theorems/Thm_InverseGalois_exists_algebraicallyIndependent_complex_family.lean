-- Prove2me | Theorems.Thm_InverseGalois_exists_algebraicallyIndependent_complex_family
-- name    : InverseGalois.exists_algebraicallyIndependent_complex_family
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-14T01:34:55.258283+00:00
-- url     : https://prove2.me/theorems/3fb8d703-f5d6-4209-a0aa-9840a96cff74
-- title:
--   Finite algebraically independent families in the complex numbers
-- statement:
--   For every finite index type $I$, there is an $I$-indexed family of complex numbers algebraically independent over the rationals:
--
--   $$
--   ∃x : I → ℂ, AI_ℚ(x).
--   $$
--
--   Here $AI_ℚ(x)$ means that the family $x$ is algebraically independent over $ℚ$. This supplies independent complex parameters for embedding finitely generated rational-function fields into $ℂ$.
-- source:
--   Mathlib, cardinality of a transcendence basis in an uncountable algebraically closed field, https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/FieldTheory/IsAlgClosed/Classification.lean#L117-L151

import Mathlib

namespace InverseGalois

theorem exists_algebraicallyIndependent_complex_family (I : Type) [Fintype I] :
    ∃ x : I → ℂ, AlgebraicIndependent ℚ x := by sorry
