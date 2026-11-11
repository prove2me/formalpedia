-- Prove2me | Theorems.Thm_NMAffExt_LBP_lemma_4_4
-- name    : NMAffExt.LBP.lemma_4_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T04:29:40.63591+00:00
-- url     : https://prove2.me/theorems/15ed03d3-bab4-466f-87e7-b46a8d06dc36
-- title:
--   Lemma 4.4 — every nonzero output parity of a $(k,\varepsilon)$ non-malleable affine extractor has $(k,2\varepsilon)$ section decorrelation
-- statement:
--   Let $1\le k<n$ and let $F:\mathbb F_2^n\to\mathbb F_2^m$ be $(k,\varepsilon)$ non-malleable against globally fixed-point-free affine involutions; in particular $F$ may be any $(k,\varepsilon)$ non-malleable affine extractor (Definition 1.1). Then for every nonzero $u\in\mathbb F_2^m$ the output parity $f_u(x)=\langle u,F(x)\rangle$ has $(k,2\varepsilon)$ section decorrelation: for every rank-$k$ linear $Q:\mathbb F_2^n\to\mathbb F_2^k$ and affine $\sigma,\tau:\mathbb F_2^k\to\mathbb F_2^n$ with $Q\sigma=Q\tau=\mathrm{id}$ and disjoint images,
--   $$\Bigl|\mathbb E_{a\sim U_k}(-1)^{f_u(\sigma(a))+f_u(\tau(a))}\Bigr|\le 2\varepsilon.$$
--
--   This is the step from the extractor guarantee to the combinatorial decorrelation condition that drives the branching-program bound of Theorem 4.8.
--
--   Differences from the source:
--   - reading: the lemma does not restate $1\le k<n$, but its conclusion is Definition 4.3, which is made only for $1\le k<n$ → hypotheses `1 ≤ k` and `k < n`; reason: the scope of the definition the conclusion refers to.
--   - reading: "Let F be a $(k,\varepsilon)$ non-malleable affine extractor … It suffices to assume non-malleability against globally fixed-point-free affine involutions" → hypothesis `IsNMAffExtInv k ε F`; reason: the lemma's last sentence; this hypothesis is implied by `IsNMAffExt k ε F`, so the statement covers both sentences.
-- source:
--   Xin Li, Yan Zhong, Non-Malleable Affine Extractors with Small Error and Complexity Lower Bounds, arXiv:2610.02407 (version of 2026-11-02, sha256 e80dad4d…), p. 56 (PDF 58), Lemma 4.4

import Mathlib
import Definitions.Def_NMAffExt_LBP_Basic
import Definitions.Def_NMAffExt_LBP_NonMalleable
import Definitions.Def_NMAffExt_LBP_SectionDecorrelation

namespace NMAffExt.LBP

/-- **Lemma 4.4.** If `F` is `(k, ε)` non-malleable against globally fixed-point-free affine
involutions (in particular, if it is a `(k, ε)` non-malleable affine extractor), then every nonzero
output parity `f_u(x) = ⟨u, F(x)⟩` has `(k, 2ε)` section decorrelation (`1 ≤ k < n`, the range of
Definition 4.3). -/
theorem lemma_4_4 (n m k : ℕ) (ε : ℝ) (F : (Fin n → ZMod 2) → (Fin m → ZMod 2))
    (hk : 1 ≤ k) (hkn : k < n) (hF : IsNMAffExtInv k ε F)
    (u : Fin m → ZMod 2) (hu : u ≠ 0) :
    HasSectionDecorrelation k (2 * ε) (parity F u) := by sorry

end NMAffExt.LBP
