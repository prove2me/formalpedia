-- Prove2me | Theorems.Thm_HighDimProbAudit_Grothendieck_tensor_power_inner
-- name    : HighDimProbAudit.Grothendieck.tensor_power_inner
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T14:35:53.237818+00:00
-- url     : https://prove2.me/theorems/379b06dd-176f-4dcd-9746-fe94ce2e156f
-- title:
--   Exercise 3.7.4 — inner products of tensor powers
-- statement:
--   Let $n,k\in\mathbb N$ and $u,v\in\mathbb R^n$. Give the tensor arrays the Euclidean inner product of Definition 3.7.1. Then
--   $$\langle u^{\otimes k},v^{\otimes k}\rangle=\langle u,v\rangle^k.$$
--   This identity represents powers of the original inner product as inner products of actual tensor arrays. It includes order zero, with both sides equal to one.
--
--   Differences from the source:
--   - encoding: vectors in ℝⁿ with their Euclidean inner product → EuclideanSpace ℝ (Fin n); reason: Fin n relabels the finite coordinates; the norm and inner product are the Euclidean ones
--   - encoding: k ∈ ℕ and tensor powers → natural-number order including zero, with the empty tensor product equal to one; reason: this is the scalar order-zero convention needed by the constant coefficient in (3.29)
-- source:
--   Vershynin, High-Dimensional Probability: An Introduction with Applications in Data Science, Cambridge University Press, 2018, author-corrected electronic copy dated June 9, 2020, https://doi.org/10.1017/9781108231596, Exercise 3.7.4, printed p. 71 (PDF p. 79).

import Mathlib
import Definitions.Def_HighDimProbAudit_Grothendieck_TensorPowers

set_option autoImplicit false

namespace HighDimProbAudit.Grothendieck

/-- Exercise 3.7.4, printed p. 71 / PDF p. 79. -/
theorem tensor_power_inner (n k : ℕ) (u v : EuclideanSpace ℝ (Fin n)) :
    inner ℝ (tensorPower k u) (tensorPower k v) = (inner ℝ u v) ^ k := by sorry

end HighDimProbAudit.Grothendieck
