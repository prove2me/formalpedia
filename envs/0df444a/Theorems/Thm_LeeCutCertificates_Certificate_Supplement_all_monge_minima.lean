-- Prove2me | Theorems.Thm_LeeCutCertificates_Certificate_Supplement_all_monge_minima
-- name    : LeeCutCertificates.Certificate.Supplement.all_monge_minima
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T19:12:29.169546+00:00
-- url     : https://prove2.me/theorems/68c5d7c9-cc09-478a-b9c2-87f4c759161c
-- title:
--   Lemma 51 — All minima of a Monge matrix
-- statement:
--   For any dimensions $a,b$ and known real lower bound $\ell$, one deterministic entry-oracle program works for every full real Monge matrix $M$ with $\ell\le M_{ij}$ for all entries. It lists exactly
--
--   $$\{(i,j):M_{ij}=\ell\}$$
--
--   using at most $9b+25a$ entry evaluations, independently of the output size. The lower bound may be negative or unattained. If a dimension is zero the output is empty and no entries are evaluated. This supplies the all-minima reporting used by Theorem 52.
--
--   **Formalization Note** The referenced Monge predicate is the nonnegative adjacent density condition, equivalent by finite telescoping to $M_{ij}+M_{i'j'}\le M_{ij'}+M_{i'j}$ for $i<i'$ and $j<j'$. It adds no sign, normalization or strictness condition. Appendix A, printed p.56 (PDF p.57), supplies the exact cap. Disconnected sets of row minima are allowed.
--
--   Differences from the source:
--   - encoding: full real Monge matrices with the all-rectangle inequality → the published adjacent-density IsMonge predicate on Fin-indexed real matrices; reason: summing adjacent inequalities gives every rectangle inequality, and each adjacent case is a rectangle; the predicate bundles no other condition
--   - encoding: O(a+b) entry evaluations → at most 9b+25a actual evaluations, with zero evaluations for an empty dimension; reason: the exact Appendix A cap applies independently of output size
-- source:
--   Troy Lee, Finding and Certifying Weighted Minimum Cuts with Cut Queries, STOC 2027 submission #474 (October 2026), Lemma 51, printed p.48 (PDF p.49); Appendix A, printed pp.53–56 (PDF pp.54–57)

import Definitions.Def_LeeCutCertificates_Certificate_Supplement_OraclePrograms
import Definitions.Def_MongeApprox_Sparsify_Monge

set_option autoImplicit false

namespace LeeCutCertificates.Certificate.Supplement

theorem all_monge_minima (a b : ℕ) (ℓ : ℝ) :
    ∃ p : OracleProgram (Fin a × Fin b) (Finset (Fin a × Fin b)),
      p.Capped (9 * b + 25 * a) ∧ ((a = 0 ∨ b = 0) → p.Capped 0) ∧
      ∀ M : Matrix (Fin a) (Fin b) ℝ, MongeApprox.Sparsify.IsMonge M →
        (∀ i j, ℓ ≤ M i j) →
        ∀ ij, ij ∈ (p.run (fun z => M z.1 z.2)).1 ↔ M ij.1 ij.2 = ℓ := by sorry

end LeeCutCertificates.Certificate.Supplement
