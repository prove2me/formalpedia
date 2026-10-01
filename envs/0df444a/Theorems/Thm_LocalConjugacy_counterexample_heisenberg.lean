-- Prove2me | Theorems.Thm_LocalConjugacy_counterexample_heisenberg
-- name    : LocalConjugacy.counterexample_heisenberg
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-09-30T13:03:17.665863+00:00
-- url     : https://prove2.me/theorems/ea50fccd-8b47-468e-a965-427eeb814b67
-- title:
--   Counterexample (§1, p. 2) — Heisenberg group
-- statement:
--   We stress that the hypothesis $N\cap H\trianglelefteq N$ in Cor. 1.3 is necessary. Consider the cyclic group $J=C_6$ acting on the Heisenberg group $N$ of order $27$ as in $C_3\wr S_3$. Then $J$ and $N$ are nilpotent, $G\cong N\rtimes J$ is supersolvable of order $162$, and there exists a subgroup $H\cong C_3\times S_3$ of order $18$ that contains a conjugate of some Sylow $p$-subgroup of $J$ for each prime $p$ but not a conjugate of $J$.
-- source:
--   Michael C. Burkhart, Local conjugacy in prosolvable groups, arXiv:2609.37678v1 (29 September 2026), https://arxiv.org/pdf/2609.37678v1, p. 2, Counterexample (§1, p. 2) — Heisenberg group; standing conventions in §1.2, pp. 2–3.

import Definitions.Def_LocalConjugacy_Examples

/-
Second unnumbered counterexample, §1, p. 2. The Heisenberg and wreath-product
identifications are included explicitly, along with every stated local/global property.

This is an open draft target. The deliberate `sorry` is the target proof hole;
all definitions and the structural proofs on which the statement rests compile
without admitted proofs.
-/
universe u v
open LocalConjugacy

theorem LocalConjugacy.counterexample_heisenberg :
    ∃ (G : ProfiniteGrp.{0}) (N J H : Subgroup G),
      -- All concrete group identifications in the source are part of the target.
      Finite G ∧ Nonempty (G ≃* WreathC3S3) ∧
      Nonempty (N ≃* Heisenberg3) ∧
      Nonempty (J ≃* Multiplicative (ZMod 6)) ∧
      Nonempty (H ≃* C3 × S3) ∧
      Nat.card G = 162 ∧ Nat.card N = 27 ∧ Nat.card J = 6 ∧ Nat.card H = 18 ∧
      -- N and J form the specified internal semidirect product.
      Splits N J ∧ Group.IsNilpotent N ∧ Group.IsNilpotent J ∧ Supersolvable G ∧
      IsClosed (N : Set G) ∧ IsClosed (J : Set G) ∧ IsClosed (H : Set G) ∧
      -- The local inclusion test succeeds, but global inclusion fails.
      LocallyContains H J ∧ (¬ ∃ g : G, conjugate g J ≤ H) ∧
      ¬ IntersectionNormal N H := by sorry
