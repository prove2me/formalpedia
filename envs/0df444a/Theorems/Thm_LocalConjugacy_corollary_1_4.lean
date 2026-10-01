-- Prove2me | Theorems.Thm_LocalConjugacy_corollary_1_4
-- name    : LocalConjugacy.corollary_1_4
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-09-30T04:10:32.303986+00:00
-- url     : https://prove2.me/theorems/350c647a-9aa6-4d63-aa8b-dec1e99da3b5
-- title:
--   Corollary 1.4
-- statement:
--   Suppose a profinite semidirect product $G=N\rtimes J$ acts transitively on some nonempty set $\Omega$ with closed point stabilizers $\{G_\alpha\}_{\alpha\in\Omega}$, where $N$ is pronilpotent and either $G$ is prosupersolvable or $J$ is pronilpotent. If $N_\alpha\trianglelefteq N$ for some $\alpha\in\Omega$, and for each prime $p$, a Sylow $p$-subgroup of $J$ fixes an element of $\Omega$, then $J$ fixes an element of $\Omega$.
-- source:
--   Michael C. Burkhart, Local conjugacy in prosolvable groups, arXiv:2609.37678v1 (29 September 2026), https://arxiv.org/pdf/2609.37678v1, p. 2, Corollary 1.4; standing conventions in §1.2, pp. 2–3.

import Definitions.Def_LocalConjugacy_Groups

/-
Corollary 1.4: Ω is nonempty and carries no topology. The action is transitive
and its point stabilizers are closed; the local fixed points may depend on p.

This is an open draft target. The deliberate `sorry` is the target proof hole;
all definitions and the structural proofs on which the statement rests compile
without admitted proofs.
-/
universe u v
open LocalConjugacy

theorem LocalConjugacy.corollary_1_4 {G : ProfiniteGrp.{u}} {Ω : Type v} [MulAction G Ω] [Nonempty Ω]
    (N J : Subgroup G) (hN : IsClosed (N : Set G)) (hJ : IsClosed (J : Set G))
    (hsplit : Splits N J) (hpron : Pronilpotent N)
    (hcase : Prosupersolvable G ∨ Pronilpotent J)
    (htrans : MulAction.IsPretransitive G Ω)
    (hclosed : ∀ x : Ω, IsClosed (MulAction.stabilizer G x : Set G))
    (hnormal : ∃ x : Ω, IntersectionNormal N (MulAction.stabilizer G x))
    (hlocal : SylowFixedPoints (Ω := Ω) J) : HasFixedPoint (Ω := Ω) J := by sorry
