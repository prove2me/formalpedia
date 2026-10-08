-- Prove2me | Theorems.Thm_OAI_Erdos3_affinePairModulus_pos
-- name    : OAI.Erdos3.affinePairModulus_pos
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T11:02:17.70956+00:00
-- url     : https://prove2.me/theorems/966dfde2-75aa-4b28-9bda-35fd47896e06
-- title:
--   The affine pair modulus is positive when the two integer vectors differ
-- statement:
--   Let $J$ be a finite type, let $t,u\colon J\to\mathbb Z$ be integer vectors, and let $k\in J$ be an index with $u_k-t_k\ne 0$. Then $0<$ `affinePairModulus t u`, where `affinePairModulus t u` is the natural number $|\gcd_{j\in J}(u_j-t_j)|$, the absolute value of the content (`BohrLattice.Primitive.content`, the gcd of all coordinates) of the difference vector $u-t$.
--
--   Lean: `OAI.Erdos3.affinePairModulus_pos` in `lean/OAI/Combinatorics/Progressions/Lattices/UniformBoxResidueMass.lean` (OpenAI); the definitions it uses are in the definitions bundles `OAIErdos3B013` of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Lattices/UniformBoxResidueMass.lean#L106

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B013

namespace OAI

section

namespace Erdos3

open scoped BigOperators Matrix

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem affinePairModulus_pos {J : Type*} [Fintype J] (t u : J → ℤ) (k : J)
    (hne : u k - t k ≠ 0) : 0 < affinePairModulus t u := by
  sorry

end Erdos3
end
end OAI
