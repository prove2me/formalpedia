-- Prove2me | Theorems.Thm_LindbladStructLearn_corollary_3_7
-- name    : LindbladStructLearn.corollary_3_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T22:02:49.179207+00:00
-- url     : https://prove2.me/theorems/ab175c67-31f6-4e0e-9cbe-3b994d799ac3
-- title:
--   Corollary 3.7 — $A_k$ is invertible with $A_k^{-1} = V_k$
-- statement:
--   For $0 \le k \le n$, the matrix $A_k$ of Notation 3.2 is invertible and its inverse is the matrix $V_k$ of Notation 3.3:
--
--   $$V_kA_k = I \qquad\text{and}\qquad A_kV_k = I.$$
--
--   Thus the Lindbladian coefficients can be recovered from the first-order local Fourier coefficients by an explicit linear map.
--
--   Differences from the source: none.
-- source:
--   Lewis–Tang–Wright, Learning the structure of open quantum systems, arXiv:2606.30358 (held version, sha256 0af12079…2eb52e), Corollary 3.7, p.22

import Mathlib
import Definitions.Def_LindbladTolerant_Testing_lindblad_model
import Definitions.Def_LindbladStructLearn_Amat
import Definitions.Def_LindbladStructLearn_Vmat

set_option autoImplicit false
open scoped ComplexOrder BigOperators Matrix ENNReal NNReal

namespace LindbladStructLearn

open LindbladTolerant.Testing

/-- Corollary 3.7 (inverse of `A_k`; Lewis–Tang–Wright, *Learning the structure of open quantum systems*, arXiv:2606.30358 (held version, sha256 0af12079…2eb52e), p.22): `A_k` is invertible, and its
inverse is `A_k⁻¹ = V_k` (Notation 3.3).

**Formalization Note** `A_k` is defined by Eq. (3.13) (Notation 3.2) and `V_k` by Eqs. (3.16)–(3.17)
(`Vmat`); both are square matrices over the `k`-local pairs with `P₁ ≠ I`, for `0 ≤ k ≤ n` (the
range of both notations); invertibility with inverse `V_k` is the pair of identities `V_k A_k = 1`
and `A_k V_k = 1`. -/
theorem corollary_3_7 (n k : ℕ) (hkn : k ≤ n) :
    Vmat n k * Amat n k = 1 ∧ Amat n k * Vmat n k = 1 := by sorry

end LindbladStructLearn
