-- Prove2me | Theorems.Thm_LocalConjugacy_proposition_4_2
-- name    : LocalConjugacy.proposition_4_2
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-09-30T12:54:46.072062+00:00
-- url     : https://prove2.me/theorems/3f5695a6-641d-4806-810a-df8303a840fc
-- title:
--   Proposition 4.2
-- statement:
--   Suppose a profinite group $G$ acts transitively and with closed point stabilizers on some nonempty set $\Omega$ and that $H\leq G$ supplements some abelian $N\trianglelefteq G$. If for each prime $p$, a Sylow $p$-subgroup of $H$ fixes an element of $\Omega$, then $H$ fixes an element of $\Omega$.
-- source:
--   Michael C. Burkhart, Local conjugacy in prosolvable groups, arXiv:2609.37678v1 (29 September 2026), https://arxiv.org/pdf/2609.37678v1, p. 8, Proposition 4.2; standing conventions in §1.2, pp. 2–3.

import Definitions.Def_LocalConjugacy_Groups

/-
Proposition 4.2: an arbitrary transitive action on a nonempty set, with
closed stabilizers. The abelian normal subgroup need not act transitively.

This is an open draft target. The deliberate `sorry` is the target proof hole;
all definitions and the structural proofs on which the statement rests compile
without admitted proofs.
-/
universe u v
open LocalConjugacy

theorem LocalConjugacy.proposition_4_2 {G : ProfiniteGrp.{u}} {Ω : Type v} [MulAction G Ω] [Nonempty Ω]
    (N H : Subgroup G) [N.Normal] (hN : IsClosed (N : Set G))
    (hH : IsClosed (H : Set G)) [IsMulCommutative N]
    (hHN : Supplements N H) (htrans : MulAction.IsPretransitive G Ω)
    (hclosed : ∀ x : Ω, IsClosed (MulAction.stabilizer G x : Set G))
    (hlocal : SylowFixedPoints (Ω := Ω) H) : HasFixedPoint (Ω := Ω) H := by sorry
