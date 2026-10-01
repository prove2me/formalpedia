-- Prove2me | Theorems.Thm_LocalConjugacy_proposition_2_2
-- name    : LocalConjugacy.proposition_2_2
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-09-30T04:12:33.860976+00:00
-- url     : https://prove2.me/theorems/df928aad-b7af-4e5d-a70f-36249e2f1ad0
-- title:
--   Proposition 2.2
-- statement:
--   For a prosolvable group $J$ and a locally finite, discrete $J$-group $N$ that is also a $p$-group, suppose $J_0\trianglelefteq J$ has prime index $p_0\neq p$. Then $\operatorname{res}^{J}_{J_0}:H^1(J,N)\xrightarrow{\sim}\operatorname{inv}_J H^1(J_0,N)$ is an isomorphism.
--
--   As stipulated in §1.2, subgroup notation includes closedness, and a discrete $J$-group has a continuous action by automorphisms.
-- source:
--   Michael C. Burkhart, Local conjugacy in prosolvable groups, arXiv:2609.37678v1 (29 September 2026), https://arxiv.org/pdf/2609.37678v1, p. 3, Proposition 2.2; standing conventions in §1.2, pp. 2–3.

import Definitions.Def_LocalConjugacy_Cohomology

/-
Proposition 2.2: restriction at a closed normal subgroup of prime index
is a pointed bijection onto stable classes, with locally finite coefficients.

This is an open draft target. The deliberate `sorry` is the target proof hole;
all definitions and the structural proofs on which the statement rests compile
without admitted proofs.
-/
universe u v
open LocalConjugacy

theorem LocalConjugacy.proposition_2_2 {J : ProfiniteGrp.{u}} {N : Type v} [Group N]
    [TopologicalSpace N] [MulDistribMulAction J N] [IsTopologicalGroup N] [DiscreteTopology N]
    [ContinuousSMul J N] (hfinite : LocallyFiniteGroup N) (p p₀ : ℕ) (hp : p.Prime) (hp₀ : p₀.Prime) (hne : p₀ ≠ p)
    (hJ : Prosolvable J) (hN : IsPGroup p N) (J₀ : Subgroup J) [J₀.Normal]
    (hJ₀ : IsClosed (J₀ : Set J)) (hindex : J₀.index = p₀) :
    Function.Bijective (stableRestriction (N := N) J₀) ∧
      (stableRestriction (N := N) J₀) default = default := by sorry
