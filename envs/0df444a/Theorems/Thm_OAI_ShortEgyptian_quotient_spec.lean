-- Prove2me | Theorems.Thm_OAI_ShortEgyptian_quotient_spec
-- name    : OAI.ShortEgyptian.quotient_spec
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T23:13:43.165205+00:00
-- url     : https://prove2.me/theorems/c36be3ef-70cb-458e-977c-40a6538bd8f0
-- title:
--   The ceiling quotient $\lceil v/u\rceil$ is positive and $u\lceil v/u\rceil$ lies in $[v,v+u)$
-- statement:
--   For natural numbers $v$ and $u$, let $z(v,u)=\lceil v/u\rceil$ be the least integer that is at least the rational number $v/u$. If $v>0$ and $u>0$, then
--
--   $$
--   z(v,u)>0,\qquad v\le u\,z(v,u),\qquad u\,z(v,u)<v+u .
--   $$
--
--   In other words, $u\,z(v,u)$ is the least multiple of $u$ that is at least $v$, and it exceeds $v$ by less than $u$. This is the basic estimate behind the greedy (Fibonacci–Sylvester) algorithm for Egyptian fractions: for $0<a<b$ the unit fraction $1/\lceil b/a\rceil$ is the largest one not exceeding $a/b$, and the bounds show that the remainder $a/b-1/\lceil b/a\rceil$ has numerator $a\lceil b/a\rceil-b$ smaller than $a$.
--
--   **Formalization Note** The quotient is `quotient v u`, defined as the natural-number ceiling `Nat.ceil` of the rational number $v/u$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/ShortEgyptian/Basic.lean#L26-L39

import Mathlib
import Definitions.Def_ShortEgyptianFractions
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_Basic

open OAI OAI.ShortEgyptian

theorem OAI.ShortEgyptian.quotient_spec {v u : ℕ} (hv : 0 < v) (hu : 0 < u) :
    0 < quotient v u ∧ v ≤ u * quotient v u ∧
      u * quotient v u < v + u := by sorry
