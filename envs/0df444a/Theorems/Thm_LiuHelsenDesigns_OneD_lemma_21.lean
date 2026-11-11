-- Prove2me | Theorems.Thm_LiuHelsenDesigns_OneD_lemma_21
-- name    : LiuHelsenDesigns.OneD.lemma_21
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T11:10:00.723883+00:00
-- url     : https://prove2.me/theorems/deeef90c-96d6-45a6-b661-50eb8876de0d
-- title:
--   Lemma 21 — at most 336 symplectic generators (corrected: vector-first Kazhdan)
-- statement:
--   There is a positive κ uniform over every $\ell\ge1$. The explicit symplectic family is symmetric, generates Sp(2ℓ;𝔽₂), and satisfies
--
--   $$
--   |S_{Sp,\ell}|\le12|S_{SL,\ell}|\le336,\qquad K(Sp(2\ell;\mathbb F_2);S_{Sp,\ell})\ge\kappa.
--   $$
--
--   The twelve conjugations are the source’s actual matrices. The rank-one family is handled directly, preserving the all-rank conclusion.
--
--   Differences from the source:
--   - correction: Definition 4 puts the generator before the unit vector → the generator may depend on the unit vector; reason: for G=(Z/2)^2 and S={a,b}, rho(a)=diag(-1,1,-1), rho(b)=diag(1,-1,-1) has no invariant vector but each generator fixes a unit vector; the printed constant is 0 while the vector-first constant is sqrt(2) and the average squared-displacement constant is 2
--   - encoding: uniform O(·) and Ω(1) statements → positive constants chosen before every size, order, precision and representation they are uniform over; reason: only Theorem 1 constants and its size threshold may depend on the fixed c
--   - encoding: folded physical order, overlap embeddings and finite small-rank cases → folded coordinate reindexing, the two actual overlapping SL placements, elementary small SL families and direct Sp(2,F₂); reason: no physical wire permutation is free, and no all-rank conclusion loses the small ranks
--   - encoding: Eq. (203) uses the cyclic shift A e_a = e_(a+1) → sourceSigma transposes the imported fourteen-matrix family before folding and placement; reason: the published sigma has the opposite shift; transpose reverses it and swaps the symmetric list of block pairs; inverse-transpose is a group automorphism and every generator is an involution, so the strict referenced Kazhdan bound is unchanged
-- source:
--   Guoding Liu, Jonas Helsen, STOC 2027 submission #221 (October 2026), p. 41, Lemma 21. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/221.pdf

import Definitions.Def_LiuHelsenDesigns_OneD_groups

namespace LiuHelsenDesigns.OneD
theorem lemma_21 : ∃ κ : ℝ, 0 < κ ∧ ∀ ℓ : ℕ, 1 ≤ ℓ →
    (spGenerators ℓ).card ≤ 12 * (slGenerators ℓ).card ∧
      12 * (slGenerators ℓ).card ≤ 336 ∧
      InverseClosed (spGenerators ℓ : Set (Sp ℓ)) ∧
      Subgroup.closure (spGenerators ℓ : Set (Sp ℓ)) = ⊤ ∧
      KazhdanLower (Sp ℓ) (spGenerators ℓ : Set (Sp ℓ)) κ := by sorry
end LiuHelsenDesigns.OneD
