-- Prove2me | Theorems.Thm_MME_StothersFourth_fixedHash_incidence_sums
-- name    : MME.StothersFourth.fixedHash_incidence_sums
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-02T21:44:52.928643+00:00
-- url     : https://prove2.me/theorems/85b5c9b3-34c4-42d4-8cea-1382289aa834
-- title:
--   Exact target and collision incidence sums for the fixed Stothers hash
-- statement:
--   For the fixed Stothers affine hash over a prime modulus $p\ge9$, sum over all augmented affine hash states. Every exact target address is retained in exactly $|S|p^N$ states, so the total target incidence is
--
--   $$|T|\,|S|\,p^N.$$
--
--   Every directed target-to-ambient collision pair is retained together in at most $p^N$ states, so the total collision incidence is at most $|C|p^N$. Here $S$ lies in the lower half of the modulus. These are the first- and second-incidence estimates used by the averaging step.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication, Proceedings of the Royal Society of Edinburgh A 143(2), 2013, Lemma 3.3 and Equations (3.3)--(3.4), https://www.maths.ed.ac.uk/~sandy/a11164.pdf.

import Definitions.Def_mme_stothers_fixed_affine_hash

open MME BigOperators

set_option autoImplicit false

theorem MME.StothersFourth.fixedHash_incidence_sums
    (m p : ℕ) (hm : 0 < m) [Fact p.Prime]
    (hp9 : 9 ≤ p) (hpodd : Odd p)
    (S : Finset ℕ) (hSrange : S ⊆ Finset.range (p / 2)) :
    (∑ q ∈ MME.StothersFourth.fixedHashStateUniverse m p,
        (MME.StothersFourth.fixedExactTargetEdges
          (MME.StothersFourth.fixedHashEdgesAtState m p S q)).card) =
        (MME.StothersFourth.fixedHashAllTargetEdges m).card * S.card *
          p ^ MME.StothersFourth.fixedOuterLength m ∧
      (∑ q ∈ MME.StothersFourth.fixedHashStateUniverse m p,
        (MME.StothersFourth.fixedTargetAmbientCollisions
          (MME.StothersFourth.fixedHashEdgesAtState m p S q)).card) ≤
        (MME.StothersFourth.fixedHashAllTargetAmbientCollisions m).card *
          p ^ MME.StothersFourth.fixedOuterLength m := by
  sorry
