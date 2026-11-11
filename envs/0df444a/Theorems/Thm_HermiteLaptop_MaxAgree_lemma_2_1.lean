-- Prove2me | Theorems.Thm_HermiteLaptop_MaxAgree_lemma_2_1
-- name    : HermiteLaptop.MaxAgree.lemma_2_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T18:16:30.976431+00:00
-- url     : https://prove2.me/theorems/73a83ac2-b663-42bc-9ca4-327516234855
-- title:
--   Lemma 2.1 — the normalized separation probability (1 − P_k(ρ))/(1 − ρ) is nondecreasing on [−1/2, 1)
-- statement:
--   Fix $k\ge1$ and define, for $\rho\in[-1,1)$,
--   $$R_k(\rho)=\frac{1-P_k(\rho)}{1-\rho}.$$
--   Then $R_k$ is nondecreasing on $[-1/2,1)$. This reduces the negative-edge inequality of the edge-wise analysis from a whole interval of correlations to the single endpoint $\rho=a$.
--
--   **Formalization Note.** `MonotoneOn` on `Set.Ico (−1/2) 1`, so the junk value of division by zero at `ρ = 1` never enters.
--
--   Differences from the source: none.
-- source:
--   García-Soriano, Miyauchi, Hermite Brings a Laptop, arXiv:2609.35453 (held version, sha256 97504f90…), p. 14 (PDF 17), Lemma 2.1

import Mathlib
import Definitions.Def_HermiteLaptop_MaxAgree_KSpokes

namespace HermiteLaptop.MaxAgree

/-- Lemma 2.1: for `k ≥ 1`, `R_k(ρ) = (1 − P_k(ρ))/(1 − ρ)` is nondecreasing on `[−1/2, 1)`. -/
theorem lemma_2_1 (k : ℕ) (hk : 1 ≤ k) :
    MonotoneOn (fun ρ : ℝ => (1 - collisionProb k ρ) / (1 - ρ)) (Set.Ico (-1 / 2 : ℝ) 1) := by sorry

end HermiteLaptop.MaxAgree
