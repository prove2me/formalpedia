-- Prove2me | Theorems.Thm_FourBlockIP_FPT_lemma_5
-- name    : FourBlockIP.FPT.lemma_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:38:17.017635+00:00
-- url     : https://prove2.me/theorems/8ff73f9b-a896-400c-979b-364bc5b50b98
-- title:
--   Lemma 5 — n-fold IDP dilation (corrected: r floored at 1)
-- statement:
--   There is an absolute natural constant $a$ such that for all natural parameters $r,s,\Delta$, with $r'=\max(r,1)$, a positive integer $M$ exists satisfying
--
--   $$M\le 2^{(a(r'+s)\Delta)^{r'(r'+s)}}$$
--
--   and the entire class $n\text{-fold}(r,s,\Delta)$ has IDP after an $M$-dilation. The class ranges over every number of blocks and every family of block widths $t_i$.
--
--   The constant is chosen before every parameter. This supplies a dilation independent of the number and widths of the blocks.
--
--   Differences from the source:
--   - correction: r may be zero but the exponent r(r+s) then loses all dependence on s and Delta → r is replaced by max(r,1) in the dilation bound; reason: C2: for r=0,s=t=n=1,D=(q),b=1 with prime q exceeding a uniform M bound, M{1/q} has no lattice points although q times that set contains M; padding a zero global row covers the case
--   - reading: O((r+s)Delta) raised to r(r+s) → one absolute constant in the base of the power; reason: the typeset O parentheses close before the exponent
--   - encoding: Euclidean spaces and integer vectors with one-based coordinates → functions on Fin types with zero-based coordinates; reason: finite reindexing changes no instance
-- source:
--   Martin Koutecký, Alexandra Lassota, Koen Ligthart, 4-Block Integer Programming is in FPT, STOC 2027 submission #392 (October 2026), Lemma 5, p. 7; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/392.pdf

import Mathlib
import Definitions.Def_FourBlockIP_FPT_Polyhedra

namespace FourBlockIP.FPT

/-- Lemma 5, p. 7, corrected at r=0 (C2). An absolute constant is
chosen before all three parameters; block count and widths are unrestricted. -/
theorem lemma_5 : ∃ c : ℕ, ∀ r s delta : ℕ, ∃ M : ℕ,
    0 < M ∧ M ≤ 2 ^ ((c * (max r 1 + s) * delta) ^ (max r 1 * (max r 1 + s))) ∧
      IDPAfterDilation (nfold r s delta) M := by sorry

end FourBlockIP.FPT
