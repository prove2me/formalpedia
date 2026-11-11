-- Prove2me | Theorems.Thm_HermiteLaptop_MaxAgree_lemma_3_2
-- name    : HermiteLaptop.MaxAgree.lemma_3_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T18:18:20.02163+00:00
-- url     : https://prove2.me/theorems/b3eb7c31-2daf-4cce-ba2d-5ef3fa950628
-- title:
--   Lemma 3.2 — c_{k,m} = k Σ_{|α|=m} B_α²/(α_1!⋯α_k!) for k ≥ 2
-- statement:
--   For every $k\ge2$ and $m\in\mathbb N_0$,
--   $$c_{k,m}=k\sum_{|\alpha|=m}\frac{B_\alpha^2}{\alpha_1!\,\alpha_2!\cdots\alpha_k!},\tag{15}$$
--   where $B_\alpha=\int\varphi H_{\alpha_1}\prod_{q\ge2}K_{\alpha_q}$ uses the unnormalized Hermite polynomials. This removes the square-root normalizations.
--
--   **Formalization Note.** The sum is over `Finset.Nat.antidiagonalTuple k m`.
--
--   Differences from the source: none.
-- source:
--   García-Soriano, Miyauchi, Hermite Brings a Laptop, arXiv:2609.35453 (held version, sha256 97504f90…), p. 19 (PDF 22), Lemma 3.2

import Mathlib
import Definitions.Def_HermiteLaptop_MaxAgree_OneDim

namespace HermiteLaptop.MaxAgree

/-- Lemma 3.2: for `k ≥ 2`, `c_{k,m} = k Σ_{|α|=m} B_α²/(α_1! ⋯ α_k!)` (15). -/
theorem lemma_3_2 (k : ℕ) (hk : 2 ≤ k) (m : ℕ) :
    coeffC k m = (k : ℝ) * ∑ α ∈ Finset.Nat.antidiagonalTuple k m,
      Balpha α ^ 2 / ∏ q : Fin k, (Nat.factorial (α q) : ℝ) := by sorry

end HermiteLaptop.MaxAgree
