-- Prove2me | Theorems.Thm_LiuHelsenDesigns_OneD_lemma_23
-- name    : LiuHelsenDesigns.OneD.lemma_23
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T11:09:44.721539+00:00
-- url     : https://prove2.me/theorems/0df3a5c6-a82e-4791-80ad-a455d5801758
-- title:
--   Lemma 23 — at most 451 full-Clifford generators (corrected: vector-first Kazhdan)
-- statement:
--   There are a positive κ and a depth D independent of $n\ge1$, and a symmetric generating set S for the full H/S/CNOT Clifford group, with projective precursor S′, such that
--
--   $$
--   |S|\le|S'|+2\le451,\qquad K(Cl_n;S)\ge\kappa.
--   $$
--
--   Both central matrices $e^{i\pi/4}I$ and $e^{-i\pi/4}I$ are in S. Every generator is realized by a nearest-neighbor Clifford circuit of depth at most D. The projective precursor has at most 449 elements.
--
--   Differences from the source:
--   - correction: Definition 4 puts the generator before the unit vector → the generator may depend on the unit vector; reason: for G=(Z/2)^2 and S={a,b}, rho(a)=diag(-1,1,-1), rho(b)=diag(1,-1,-1) has no invariant vector but each generator fixes a unit vector; the printed constant is 0 while the vector-first constant is sqrt(2) and the average squared-displacement constant is 2
--   - encoding: uniform O(·) and Ω(1) statements → positive constants chosen before every size, order, precision and representation they are uniform over; reason: only Theorem 1 constants and its size threshold may depend on the fixed c
--   - reading: |S_Cl,ℓ| ≤ |S′_Cl,ℓ| + 2 ≤ 451, with S′_Cl,ℓ the symmetric projective set of p.46 and S_Cl,ℓ = Ŝ_Cl,ℓ ∪ Ω of Eq. (263) → some S′ ⊆ PCl with |S′| ≤ 449 whose union with {1} is the projective image of S, and S contains e^{±iπ/4}I; reason: clause 1 names S′_Cl,ℓ of the construction on p.46; these conclusions tie S′ and S to that construction and do not weaken the clause
-- source:
--   Guoding Liu, Jonas Helsen, STOC 2027 submission #221 (October 2026), p. 46, Lemma 23. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/221.pdf

import Definitions.Def_LiuHelsenDesigns_OneD_groups

namespace LiuHelsenDesigns.OneD
attribute [local instance] Classical.decEq
theorem lemma_23 : ∃ (κ : ℝ) (D : ℕ), 0 < κ ∧
    ∀ n : ℕ, 1 ≤ n → ∃ S : Finset (Cl n), S.card ≤ 451 ∧
      InverseClosed (S : Set (Cl n)) ∧ Subgroup.closure (S : Set (Cl n)) = ⊤ ∧
      KazhdanLower (Cl n) (S : Set (Cl n)) κ ∧
      (∃ S' : Finset (PCl n), S'.card ≤ 449 ∧ S.card ≤ S'.card+2 ∧
        S.image (projectivize n) = insert 1 S') ∧
      (∃ Uplus Uminus : Cl n,
        ((Uplus.val : Unitary n) : Mat n) = Complex.exp (Complex.I*(Real.pi/4)) • 1 ∧
        ((Uminus.val : Unitary n) : Mat n) = Complex.exp (-Complex.I*(Real.pi/4)) • 1 ∧
        Uplus ∈ S ∧ Uminus ∈ S) ∧
      ∀ U ∈ S, ∃ C : Circuit, RepresentsCl n C U ∧ depth C ≤ D := by sorry
end LiuHelsenDesigns.OneD
