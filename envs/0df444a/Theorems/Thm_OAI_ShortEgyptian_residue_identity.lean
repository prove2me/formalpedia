-- Prove2me | Theorems.Thm_OAI_ShortEgyptian_residue_identity
-- name    : OAI.ShortEgyptian.residue_identity
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T23:14:14.451556+00:00
-- url     : https://prove2.me/theorems/4e7a4d46-32db-4f2b-83f0-a80788dd2e55
-- title:
--   One greedy step against a divisor: $\frac{u}{MQ}=\frac{1}{(M/t)z}+\frac{h}{MQz}$
-- statement:
--   For natural numbers $v,u$ write $z(v,u)=\lceil v/u\rceil$ for the least integer that is at least $v/u$, and $r(v,u)=u\,z(v,u)-v$ for the corresponding residue; for $u,v>0$ one has $v\le u\,z(v,u)<v+u$, so $r(v,u)$ is the least non-negative residue of $-v$ modulo $u$.
--
--   Let $M,Q,u,t$ be positive integers with $t\mid M$, and put $z=z(Qt,u)$ and $h=r(Qt,u)=uz-Qt$. Then, in $\mathbb{Q}$,
--
--   $$
--   \frac{u}{MQ}=\frac{1}{(M/t)\,z}+\frac{h}{MQz}.
--   $$
--
--   Thus subtracting the unit fraction $1/\big((M/t)z\big)$ from $u/(MQ)$ leaves a fraction whose numerator is the residue $h$, which is smaller than $u$, and whose denominator is $MQ$ multiplied by $z$. In residue-descent arguments for short Egyptian fraction expansions this identity is the step that replaces a numerator $u$ by a smaller residue $h$, the divisor $t$ of the fixed modulus $M$ being chosen so that $h$ is small.
--
--   **Formalization Note** Here $z$ and $h$ are `quotient (Q * t) u` and `residue (Q * t) u z`, where `residue v u z = u * z - v` uses truncated natural subtraction; no truncation occurs because $uz\ge Qt$. The quotient $M/t$ is natural-number division, which is exact because $t\mid M$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/ShortEgyptian/Basic.lean#L48-L69

import Mathlib
import Definitions.Def_ShortEgyptianFractions
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_Basic

open OAI OAI.ShortEgyptian

theorem OAI.ShortEgyptian.residue_identity {M Q u t : ℕ} (hM : 0 < M) (hQ : 0 < Q)
    (hu : 0 < u) (ht : 0 < t) (htM : t ∣ M) :
    let z := quotient (Q * t) u
    let h := residue (Q * t) u z
    (u : ℚ) / (M * Q) =
      1 / ((M / t : ℕ) * (z : ℚ)) + (h : ℚ) / (M * Q * z) := by sorry
