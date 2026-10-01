-- Prove2me | Theorems.Thm_LocalConjugacy_proposition_2_3
-- name    : LocalConjugacy.proposition_2_3
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-09-30T12:38:46.05674+00:00
-- url     : https://prove2.me/theorems/7db83901-9d00-46eb-b511-3faa03cf8ed9
-- title:
--   Proposition 2.3
-- statement:
--   For a profinite group $J$ and a finite $J$-group $N$ that is also a $p$-group, suppose $NJ$ is prosupersolvable. Let $\pi$ denote the set of primes not exceeding $p$ and let $Q$ be a Hall $\pi$-subgroup of $J$. Then $\operatorname{res}^{J}_{Q}:H^1(J,N)\xrightarrow{\sim}H^1(Q,N)$ is an isomorphism.
--
--   As stipulated in §1.2, subgroup notation includes closedness, and a discrete $J$-group has a continuous action by automorphisms.
-- source:
--   Michael C. Burkhart, Local conjugacy in prosolvable groups, arXiv:2609.37678v1 (29 September 2026), https://arxiv.org/pdf/2609.37678v1, p. 4, Proposition 2.3; standing conventions in §1.2, pp. 2–3.

import Definitions.Def_LocalConjugacy_Cohomology

/-
Proposition 2.3: the arXiv version assumes profinite J and prosupersolvable NJ.
There is no additional prosolvability hypothesis. Q is any Hall subgroup for
the primes at most p, and the codomain is all H¹(Q,N), not just stable classes.

This is an open draft target. The deliberate `sorry` is the target proof hole;
all definitions and the structural proofs on which the statement rests compile
without admitted proofs.
-/
universe u v
open LocalConjugacy

theorem LocalConjugacy.proposition_2_3 {J : ProfiniteGrp.{u}} {N : Type v} [Group N]
    [TopologicalSpace N] [MulDistribMulAction J N] [DiscreteTopology N] [Finite N]
    [ContinuousSMul J N] (p : ℕ) (hp : p.Prime) (hN : IsPGroup p N)
    (hG : Prosupersolvable (ActionProduct J N))
    (Q : Subgroup J) (hQ : IsHallPro {r | r ≤ p} Q) :
    Function.Bijective (restrictH1 (N := N) (show Q ≤ ⊤ from le_top)) ∧
      (restrictH1 (N := N) (show Q ≤ ⊤ from le_top)) default = default := by sorry
