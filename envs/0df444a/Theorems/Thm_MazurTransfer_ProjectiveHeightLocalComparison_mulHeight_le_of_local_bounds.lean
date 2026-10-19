-- Prove2me | Theorems.Thm_MazurTransfer_ProjectiveHeightLocalComparison_mulHeight_le_of_local_bounds
-- name    : MazurTransfer.ProjectiveHeightLocalComparison.mulHeight_le_of_local_bounds
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-17T01:15:19.993103+00:00
-- url     : https://prove2.me/theorems/facb3bc8-9a5c-4be4-800e-75aacb7419e9
-- title:
--   A projective height bound from local bounds on three tuples
-- statement:
--   Let $K$ be a field equipped with admissible absolute values, and let $u$, $b$, and $t$ be nonzero tuples in $K$, each indexed by a finite type. For an absolute value $v$, write $M_v(t)=\max_j v(t_j)$, and similarly for $u$ and $b$. Let $C\ge1$. Suppose
--   $$M_v(t)\le C M_v(b)M_v(u)$$
--   at every archimedean place and
--   $$M_v(t)\le M_v(b)M_v(u)$$
--   at every nonarchimedean place. Then the multiplicative projective heights satisfy
--   $$H(t)\le C^{W_K}H(b)H(u),$$
--   where $W_K$ is the total archimedean weight of the admissible absolute-value system.
--
--   The comparison globalizes local polynomial-root or section-value estimates. In the order-thirteen Picard descent it converts the actual monic theta norm equations into a global height bound.
-- source:
--   Original general local-to-global comparison by Vas and contributors, October 17, 2026; exact source ProjectiveHeightLocalComparison.lean SHA256 29f8d19b3304b336250fea7a9c4d0c7242cb954ee85814155845e227d522c00a. The product-formula proof is adapted from Michael Stoll, Height.mulHeight_linearMap_apply_le (2026, Apache-2.0): https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/NumberTheory/Height/MvPolynomial.lean#L121-L156. The present statement is a generalization from linear maps to arbitrary tuples satisfying the stated local bounds.

import Mathlib
open Height Height.AdmissibleAbsValues Multiset
universe vK vI vB vT

theorem MazurTransfer.ProjectiveHeightLocalComparison.mulHeight_le_of_local_bounds {K : Type vK} {ι : Type vI} {κ : Type vB} {τ : Type vT}
    [Field K] [AdmissibleAbsValues K] [Finite ι] [Finite κ] [Finite τ]
    (u : ι → K) (b : κ → K) (t : τ → K)
    (hu : u ≠ 0) (hb : b ≠ 0) (ht : t ≠ 0) (C : ℝ) (hC : 1 ≤ C)
    (ha : ∀ v ∈ archAbsVal (K := K),
      ⨆ j, v (t j) ≤ C * (⨆ k, v (b k)) * ⨆ i, v (u i))
    (hn : ∀ v : nonarchAbsVal (K := K),
      ⨆ j, v.val (t j) ≤ (⨆ k, v.val (b k)) * ⨆ i, v.val (u i)) :
    mulHeight t ≤ C ^ totalWeight K * mulHeight b * mulHeight u := by sorry
