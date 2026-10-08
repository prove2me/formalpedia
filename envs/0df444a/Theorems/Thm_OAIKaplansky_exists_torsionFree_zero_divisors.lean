-- Prove2me | Theorems.Thm_OAIKaplansky_exists_torsionFree_zero_divisors
-- name    : OAIKaplansky.exists_torsionFree_zero_divisors
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-07T15:11:00.087925+00:00
-- url     : https://prove2.me/theorems/a16f2c8c-8c08-4b34-98f0-515ec456b6d0
-- title:
--   Theorem 1.1 (OpenAI) — a finitely presented torsion-free group $G$ with zero divisors in $\mathbb F_2[G]$
-- statement:
--   There exist a finitely presented group $G$ in which every element of finite order is the identity, and nonzero elements $\alpha,\beta$ of the group algebra $\mathbb F_2[G]$, such that
--
--   $$\alpha\beta=0 .$$
--
--   This refutes Kaplansky's zero-divisor conjecture, which asserts that $K[G]$ has no nonzero zero divisors whenever $K$ is a field and $G$ is torsion-free. The counterexample has $K=\mathbb F_2$. Finite-order elements give zero divisors trivially, since $(1-g)(1+g+\dots+g^{m-1})=0$ when $g^m=1$. The theorem shows that excluding them is not enough.
--
--   OpenAI, *A Torsion-Free Group Algebra with Zero Divisors* (September 23, 2026), p. 1: “Theorem 1.1. There exist a finitely presented torsion-free group $G$ and nonzero elements $\alpha, \beta \in \mathbb F_2[G]$ such that $\alpha\beta = 0$. Moreover, $G$ admits a finite two-dimensional classifying space.”
--
--   The group is the fundamental group of two random finite graphs, immersed in a rose and coned off. The factors are sums of path labels from two roots. The construction, the proof and the Lean formalization are OpenAI's ([github.com/openai/math](https://github.com/openai/math)). The proof on this platform assembles the published lemmas `OAI.TorsionFreeZeroDivisors.SampleGraph.exists_avoiding`, `OAI.TorsionFreeZeroDivisors.SampleGraph.SpherePicture.excluded`, `OAI.TorsionFreeZeroDivisors.ConeTorsion.graph_torsion_free` and `OAI.TorsionFreeZeroDivisors.ConcreteFactors.both_nonzero`.
--
--   **Formalization note.** Only Mathlib notions are used. $G$ is a group in `Type`, finitely presented in the sense of `Group.IsFinitelyPresented`: a quotient of a free group on finitely many generators by the normal closure of finitely many relators. Torsion-freeness is stated as $\mathrm{IsOfFinOrder}(g)\Rightarrow g=1$, so every element of finite order is trivial. This is the paper's notion, not Mathlib's stronger `IsMulTorsionFree`, which asks for unique roots. $\mathbb F_2[G]$ is `MonoidAlgebra (ZMod 2) G`. The “Moreover” clause, a finite two-dimensional $K(G,1)$, is omitted. The full statement, with that clause, is published separately, as an open statement, as [`OAI.TorsionFreeZeroDivisors.main`](https://prove2.me/theorems/1176303a-4023-4bb7-91dd-bb08698d0409).
-- source:
--   OpenAI, A Torsion-Free Group Algebra with Zero Divisors, OpenAI Math Release, September 23, 2026, https://github.com/openai/math/blob/main/preprints/A-Torsion-Free-Group-Algebra-with-Zero-Divisors-September-23-2026/paper.pdf, p. 1, Theorem 1.1 (without its classifying-space clause); Lean: https://github.com/openai/math, lean/OAI/Algebra/GroupRing (Apache-2.0), TorsionFreeZeroDivisors.torsion_free_finitely_presented_zero_divisors

import Mathlib

namespace OAIKaplansky

theorem exists_torsionFree_zero_divisors :
    ∃ (G : Type) (_ : Group G), Group.IsFinitelyPresented G ∧
      (∀ g : G, IsOfFinOrder g → g = 1) ∧
      ∃ α β : MonoidAlgebra (ZMod 2) G, α ≠ 0 ∧ β ≠ 0 ∧ α * β = 0 := by
  sorry

end OAIKaplansky
