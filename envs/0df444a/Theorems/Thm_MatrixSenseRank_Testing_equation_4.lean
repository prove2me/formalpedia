-- Prove2me | Theorems.Thm_MatrixSenseRank_Testing_equation_4
-- name    : MatrixSenseRank.Testing.equation_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T13:47:13.368234+00:00
-- url     : https://prove2.me/theorems/93d1e3aa-163a-47cf-8ee1-619d1624859d
-- title:
--   §1.2, Eq. (4) — normalized rank distance
-- statement:
--   Let $n,m$ be natural numbers and $1\le k\le\min(n,m)$ (so both are positive), and let $A$ be any real $n\times m$ matrix with $\|A\|_F=1$. Write $\tau_k=\sum_{i>k}\sigma_i(A)^2$ for the squared singular-value tail and use the unit-Frobenius feasible set in the definition of $\operatorname{dist}_k(A)$. Then
--   $$\operatorname{dist}_k(A)^2=2-2\sqrt{1-\tau_k},\qquad
--   \tau_k\le\operatorname{dist}_k(A)^2\le2\tau_k.$$
--   This bridges normalized low-rank approximation and the relative sparsity distance of singular values. The identity is a theorem, not a defining assumption on distance or singular values.
--
--   Differences from the source:
--   - encoding: one-based singular values and unit-Frobenius distance in Eqs. (3)–(4) → finite zero-based tail with published sv evaluated only at i+1, and distance defined by the actual feasible-set infimum; reason: finite reindexing preserves every singular value and unit-norm approximant; positivity and the k-domain are the standing assumptions of §1.2
-- source:
--   Yiqiao Bao, Anindya De, Shivam Nadimpalli, Rocco A. Servedio, Chenyang Sun, Nathan White, STOC 2027 submission #380 (October 2026), §1.2, Eq. (4), printed p. 2 / PDF p. 3; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/380.pdf; PDF SHA-256 6e4e46ced4dfe65bbe94e4cec3e8230032914efef9d87b0f544bbea151a00c3b.

import Mathlib
import Definitions.Def_MatrixSenseRank_Testing_Geometry

set_option autoImplicit false

namespace MatrixSenseRank.Testing

/-- §1.2, Eq. (4), printed p. 2 / PDF p. 3. Both bounds and the identity are retained. -/
theorem equation_4 (n m k : ℕ)
    (hk : 1 ≤ k) (hkn : k ≤ min n m) (A : Matrix (Fin n) (Fin m) ℝ)
    (hA : frobenius A = 1) :
    rankDistance k A ^ 2 = 2 - 2 * Real.sqrt (1 - singularTail k A) ∧
    singularTail k A ≤ rankDistance k A ^ 2 ∧
    rankDistance k A ^ 2 ≤ 2 * singularTail k A := by sorry

end MatrixSenseRank.Testing
