-- Prove2me | Theorems.Thm_LiuHelsenDesigns_OneD_lemma_17
-- name    : LiuHelsenDesigns.OneD.lemma_17
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T11:09:53.028933+00:00
-- url     : https://prove2.me/theorems/79b01518-9944-4894-b739-f78c59379e39
-- title:
--   Lemma 17 — at most 28 special-linear generators (corrected: vector-first Kazhdan)
-- statement:
--   There is a positive κ independent of ℓ such that for every $\ell\ge6$ the actual folded elementary family $S_{SL,\ell}$ is symmetric, generates SL(ℓ;𝔽₂), and satisfies
--
--   $$
--   |S_{SL,\ell}|\le28,\qquad K(SL(\ell;\mathbb F_2);S_{SL,\ell})\ge\kappa.
--   $$
--
--   Two overlapping blocks handle ranks not divisible by three. The existing Open Kassabov bound remains a proof obligation.
--
--   Differences from the source:
--   - correction: Definition 4 puts the generator before the unit vector → the generator may depend on the unit vector; reason: for G=(Z/2)^2 and S={a,b}, rho(a)=diag(-1,1,-1), rho(b)=diag(1,-1,-1) has no invariant vector but each generator fixes a unit vector; the printed constant is 0 while the vector-first constant is sqrt(2) and the average squared-displacement constant is 2
--   - encoding: uniform O(·) and Ω(1) statements → positive constants chosen before every size, order, precision and representation they are uniform over; reason: only Theorem 1 constants and its size threshold may depend on the fixed c
--   - encoding: folded physical order, overlap embeddings and finite small-rank cases → folded coordinate reindexing, the two actual overlapping SL placements, elementary small SL families and direct Sp(2,F₂); reason: no physical wire permutation is free, and no all-rank conclusion loses the small ranks
--   - encoding: Eq. (203) uses the cyclic shift A e_a = e_(a+1) → sourceSigma transposes the imported fourteen-matrix family before folding and placement; reason: the published sigma has the opposite shift; transpose reverses it and swaps the symmetric list of block pairs; inverse-transpose is a group automorphism and every generator is an involution, so the strict referenced Kazhdan bound is unchanged
--   - generalization: there exists a symmetric generating set S_SL,ℓ → the explicit set slGenerators ℓ of the proof (the Eq. (205) family, folded and placed on A⊕B and B⊕C, pp.37 and 41); reason: a specific witness implies the existential statement
-- source:
--   Guoding Liu, Jonas Helsen, STOC 2027 submission #221 (October 2026), p. 36, Lemma 17. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/221.pdf

import Definitions.Def_LiuHelsenDesigns_OneD_groups

namespace LiuHelsenDesigns.OneD
theorem lemma_17 : ∃ κ : ℝ, 0 < κ ∧ ∀ ℓ : ℕ, 6 ≤ ℓ →
    (slGenerators ℓ).card ≤ 28 ∧ InverseClosed (slGenerators ℓ : Set (SL ℓ)) ∧
      Subgroup.closure (slGenerators ℓ : Set (SL ℓ)) = ⊤ ∧
      KazhdanLower (SL ℓ) (slGenerators ℓ : Set (SL ℓ)) κ := by sorry
end LiuHelsenDesigns.OneD
