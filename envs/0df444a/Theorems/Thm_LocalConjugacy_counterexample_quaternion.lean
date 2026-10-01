-- Prove2me | Theorems.Thm_LocalConjugacy_counterexample_quaternion
-- name    : LocalConjugacy.counterexample_quaternion
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-09-30T13:00:30.427974+00:00
-- url     : https://prove2.me/theorems/c3e68c4b-469f-454e-b139-55c5751bda04
-- title:
--   Counterexample (§1, p. 2) — quaternion group
-- statement:
--   Losey and Stonehewer [7, Sec. 3] provide the example of $J=S_3$ operating on $N=Q_8$ as in $GL(2,3)$. In this case, there is a complement $J'$ to $N$ that is locally conjugate but not conjugate to $J$; $H^1(J,N)$ has order two while $H^1(J_p,N)$ is trivial for each Sylow $p$-subgroup $J_p$ of $J$. Thus, even for finite groups, requiring $J$ to be solvable or even supersolvable is not sufficient.
-- source:
--   Michael C. Burkhart, Local conjugacy in prosolvable groups, arXiv:2609.37678v1 (29 September 2026), https://arxiv.org/pdf/2609.37678v1, p. 2, Counterexample (§1, p. 2) — quaternion group; standing conventions in §1.2, pp. 2–3.

import Definitions.Def_LocalConjugacy_Examples

/-
First unnumbered counterexample, §1, p. 2. The matrix-group identification,
cohomology cardinalities, and failure of conjugacy are all asserted together.

This is an open draft target. The deliberate `sorry` is the target proof hole;
all definitions and the structural proofs on which the statement rests compile
without admitted proofs.
-/
universe u v
open LocalConjugacy

theorem LocalConjugacy.counterexample_quaternion :
    ∃ a : S3 →* MulAut Q8,
      -- The action is realized in the matrix group named in the source.
      Nonempty ((Q8 ⋊[a] S3) ≃* GL (Fin 2) (ZMod 3)) ∧
      -- There are exactly two global cohomology classes.
      Nat.card (FiniteH1 a) = 2 ∧
      -- Every Sylow restriction has trivial first cohomology.
      (∀ (p : ℕ) (hp : p.Prime),
        letI : Fact p.Prime := ⟨hp⟩
        ∀ P : Sylow p S3, Subsingleton (FiniteH1 (a.comp P.toSubgroup.subtype))) ∧
      -- The same action gives the locally conjugate, nonconjugate complements.
      ∃ J' : Subgroup (Q8 ⋊[a] S3),
        (quaternionKernel a).IsComplement' J' ∧
        FiniteLocallyConjugate (quaternionComplement a) J' ∧
        ¬ Conjugate (quaternionComplement a) J' := by sorry
