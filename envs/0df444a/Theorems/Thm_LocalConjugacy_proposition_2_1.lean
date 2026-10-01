-- Prove2me | Theorems.Thm_LocalConjugacy_proposition_2_1
-- name    : LocalConjugacy.proposition_2_1
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-09-30T04:11:43.097412+00:00
-- url     : https://prove2.me/theorems/3a4adb50-a11e-4df4-851b-09a4d9ce0999
-- title:
--   Proposition 2.1
-- statement:
--   For a profinite group $J$ and a locally finite, discrete $J$-group $N$ that is also a $p$-group, suppose $Q\leq J$ is a procyclic $p_0$-group for some prime $p_0\neq p$ and that $J_0\trianglelefteq J$. If $\varphi\in Z^1(J_0,N)$ is $Q$-invariant, then there exists $\psi\in Z^1(J_0,N)$ with $\psi\sim\varphi$ such that $\psi^q=\psi$ for all $q\in Q$. Furthermore, $\psi(q)=1$ for all $q\in J_0\cap Q$.
--
--   As stipulated in §1.2, subgroup notation includes closedness, and a discrete $J$-group has a continuous action by automorphisms.
-- source:
--   Michael C. Burkhart, Local conjugacy in prosolvable groups, arXiv:2609.37678v1 (29 September 2026), https://arxiv.org/pdf/2609.37678v1, p. 3, Proposition 2.1; standing conventions in §1.2, pp. 2–3.

import Definitions.Def_LocalConjugacy_Cohomology

/-
Proposition 2.1: discrete coefficients may be infinite but are locally finite.
The new cocycle is fixed literally by Q and is trivial on J₀ ∩ Q.

This is an open draft target. The deliberate `sorry` is the target proof hole;
all definitions and the structural proofs on which the statement rests compile
without admitted proofs.
-/
universe u v
open LocalConjugacy

theorem LocalConjugacy.proposition_2_1 {J : ProfiniteGrp.{u}} {N : Type v} [Group N]
    [TopologicalSpace N] [MulDistribMulAction J N] [IsTopologicalGroup N] [DiscreteTopology N]
    [ContinuousSMul J N] (hfinite : LocallyFiniteGroup N) (p p₀ : ℕ) (hp : p.Prime) (hp₀ : p₀.Prime) (hne : p₀ ≠ p)
    (hN : IsPGroup p N) (J₀ Q : Subgroup J) [J₀.Normal]
    (hJ₀ : IsClosed (J₀ : Set J)) (hQ : IsClosed (Q : Set J))
    (hcyclic : Procyclic Q) (hpro : IsProP p₀ Q)
    (f : Cocycle (N := N) J₀) (hinv : InvariantUnder Q J₀ f) :
    ∃ g : Cocycle (N := N) J₀, Cohomologous f g ∧
      (∀ (q : J) (hq : q ∈ Q) (x : J) (hx : x ∈ J₀)
        (hqx : q⁻¹ * x * q ∈ J₀),
        q • g.toFun ⟨q⁻¹ * x * q, hqx⟩ = g.toFun ⟨x, hx⟩) ∧
      ∀ (q : J) (hq : q ∈ Q) (hq₀ : q ∈ J₀), g.toFun ⟨q, hq₀⟩ = 1 := by sorry
