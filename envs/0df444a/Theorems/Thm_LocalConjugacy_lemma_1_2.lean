-- Prove2me | Theorems.Thm_LocalConjugacy_lemma_1_2
-- name    : LocalConjugacy.lemma_1_2
-- status  : Open
-- author  : @burkh4rt
-- created : 2026-09-30T04:01:48.73662+00:00
-- url     : https://prove2.me/theorems/30bd1fa6-280e-4576-9eaf-460e7e5cb998
-- title:
--   Lemma 1.2
-- statement:
--   For a profinite group $J$ and a finite nilpotent $J$-group $N$, if either $NJ$ is prosupersolvable or $J$ is pronilpotent, the map $\varphi \mapsto \times_{p\in\pi(J)}\varphi|_{J_p}$ induces an isomorphism $H^1(J,N)\cong\times_{p\in\pi(J)}\operatorname{inv}_J H^1(J_p,N)$ of pointed sets, where $J_p\in\operatorname{Syl}_p(J)$ for each $p\in\pi(J)$.
-- source:
--   Michael C. Burkhart, Local conjugacy in prosolvable groups, arXiv:2609.37678v1 (29 September 2026), https://arxiv.org/pdf/2609.37678v1, p. 2, Lemma 1.2; standing conventions in §1.2, pp. 2–3.

import Definitions.Def_LocalConjugacy_Cohomology

/-
Lemma 1.2: the simultaneous restriction map on actual H¹ classes is a pointed
bijection to the full product of stable classes. N is finite and nilpotent.

This is an open draft target. The deliberate `sorry` is the target proof hole;
all definitions and the structural proofs on which the statement rests compile
without admitted proofs.
-/
universe u v
open LocalConjugacy

theorem LocalConjugacy.lemma_1_2 {J : ProfiniteGrp.{u}} {N : Type v} [Group N]
    [TopologicalSpace N] [MulDistribMulAction J N] [DiscreteTopology N] [Finite N] [Group.IsNilpotent N]
    [ContinuousSMul J N]
    (hcase : Prosupersolvable (ActionProduct J N) ∨ Pronilpotent J)
    (P : PrimeDivisor J → Subgroup J) (hP : ∀ p, IsSylowPro p.val.val ⊤ (P p)) :
    Function.Bijective (primaryRestriction (N := N) P) ∧
      (primaryRestriction (N := N) P) default = default := by sorry
