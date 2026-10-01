-- Prove2me | Theorems.Thm_LocalConjugacy_corollary_1_3
-- name    : LocalConjugacy.corollary_1_3
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-09-30T04:06:26.585441+00:00
-- url     : https://prove2.me/theorems/5a2265c7-142c-4414-9581-ad547a4d599b
-- title:
--   Corollary 1.3
-- statement:
--   Let $H$ be a closed subgroup of a profinite semidirect product $G=N\rtimes J$ where $N$ is pronilpotent and either $G$ is prosupersolvable or $J$ is pronilpotent. If $N\cap H\trianglelefteq N$ and $H$ contains a conjugate of some Sylow $p$-subgroup of $J$ for each prime $p$, then $H$ contains a conjugate of $J$.
-- source:
--   Michael C. Burkhart, Local conjugacy in prosolvable groups, arXiv:2609.37678v1 (29 September 2026), https://arxiv.org/pdf/2609.37678v1, p. 2, Corollary 1.3; standing conventions in §1.2, pp. 2–3.

import Definitions.Def_LocalConjugacy_Groups

/-
Corollary 1.3: an internal complement models the profinite semidirect product.
Normality of N ∩ H is required inside N, and local witnesses may vary with p.

This is an open draft target. The deliberate `sorry` is the target proof hole;
all definitions and the structural proofs on which the statement rests compile
without admitted proofs.
-/
universe u v
open LocalConjugacy

theorem LocalConjugacy.corollary_1_3 {G : ProfiniteGrp.{u}} (N J H : Subgroup G)
    (hN : IsClosed (N : Set G)) (hJ : IsClosed (J : Set G))
    (hH : IsClosed (H : Set G)) (hsplit : Splits N J)
    (hpron : Pronilpotent N) (hcase : Prosupersolvable G ∨ Pronilpotent J)
    (hnormal : IntersectionNormal N H) (hlocal : LocallyContains H J) :
    ∃ g : G, conjugate g J ≤ H := by sorry
