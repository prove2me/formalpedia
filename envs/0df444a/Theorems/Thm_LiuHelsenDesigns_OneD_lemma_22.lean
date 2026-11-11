-- Prove2me | Theorems.Thm_LiuHelsenDesigns_OneD_lemma_22
-- name    : LiuHelsenDesigns.OneD.lemma_22
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T11:09:42.317761+00:00
-- url     : https://prove2.me/theorems/3f5f099e-0610-48bc-98b9-e604110d3bfc
-- title:
--   Lemma 22 — at most 337 projective-Clifford generators (corrected: vector-first Kazhdan)
-- statement:
--   For every $n\ge1$, choose any projective Clifford lift f of the actual symplectic family. Adjoin Pauli X on the first physical qubit and write S=f(S_Sp)∪{X₁}. Uniform positive κ and constant depth D can be chosen such that
--
--   $$
--   |S|\le|S_{Sp}|+1\le337,\qquad\langle S\rangle=\overline{Cl}_n,\qquad K(\overline{Cl}_n;S)\ge\kappa.
--   $$
--
--   Every generator has a nearest-neighbor Clifford realization of depth at most D. No homomorphism property of the lift is assumed.
--
--   Differences from the source:
--   - correction: Definition 4 puts the generator before the unit vector → the generator may depend on the unit vector; reason: for G=(Z/2)^2 and S={a,b}, rho(a)=diag(-1,1,-1), rho(b)=diag(1,-1,-1) has no invariant vector but each generator fixes a unit vector; the printed constant is 0 while the vector-first constant is sqrt(2) and the average squared-displacement constant is 2
--   - encoding: uniform O(·) and Ω(1) statements → positive constants chosen before every size, order, precision and representation they are uniform over; reason: only Theorem 1 constants and its size threshold may depend on the fixed c
--   - encoding: folded physical order, overlap embeddings and finite small-rank cases → folded coordinate reindexing, the two actual overlapping SL placements, elementary small SL families and direct Sp(2,F₂); reason: no physical wire permutation is free, and no all-rank conclusion loses the small ranks
--   - reading: a Clifford lift f, specified as any right inverse in Eq.(252) → any projective Clifford representatives with the stated symplectic action; reason: different lifts differ by a Pauli correction of constant parallel depth; Eq.(253) alone does not uniquely fix that correction
--   - encoding: Eq. (203) uses the cyclic shift A e_a = e_(a+1) → sourceSigma transposes the imported fourteen-matrix family before folding and placement; reason: the published sigma has the opposite shift; transpose reverses it and swaps the symmetric list of block pairs; inverse-transpose is a group automorphism and every generator is an involution, so the strict referenced Kazhdan bound is unchanged
-- source:
--   Guoding Liu, Jonas Helsen, STOC 2027 submission #221 (October 2026), p. 43, Lemma 22. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/221.pdf

import Definitions.Def_LiuHelsenDesigns_OneD_groups

namespace LiuHelsenDesigns.OneD
theorem lemma_22 : ∃ (κ : ℝ) (D : ℕ), 0 < κ ∧ ∀ n : ℕ, 1 ≤ n →
    ∀ f : Sp n → PCl n, (∀ g : Sp n, HasProjectiveAction (f g) g) →
      (projectiveLiftSet n f).ncard ≤ (spGenerators n).card + 1 ∧
      (spGenerators n).card + 1 ≤ 337 ∧
      Subgroup.closure (projectiveLiftSet n f) = ⊤ ∧
      KazhdanLower (PCl n) (projectiveLiftSet n f) κ ∧
      ∀ U ∈ projectiveLiftSet n f, ∃ C : Circuit,
        RepresentsPCl n C U ∧ depth C ≤ D := by sorry
end LiuHelsenDesigns.OneD
