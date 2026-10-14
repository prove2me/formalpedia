-- Prove2me | Theorems.Thm_GarrettFA_isVonNBounded_iff_of_isStrictColimit
-- name    : GarrettFA.isVonNBounded_iff_of_isStrictColimit
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-12T19:28:41.330265+00:00
-- url     : https://prove2.me/theorems/38c6b470-8d12-4818-b729-4407b564289e
-- title:
--   Prop. 2.1.1 — bounded sets in strict colimits
-- statement:
--   Let $V$ be a locally convex space over $\mathbb K=\mathbb R$ or $\mathbb C$ that is the strict colimit of a chain of closed subspaces $V_0\subsetneq V_1\subsetneq\cdots$. Then a subset $B\subseteq V$ is bounded if and only if
--
--   $$\exists\, i:\quad B\subseteq V_i\ \text{ and } B \text{ is bounded in } V_i .$$
--
--   This is the Dieudonné–Schwartz description of bounded sets. It reduces boundedness, and hence quasi-completeness, in an LF-space to its Fréchet steps.
--
--   **Formalization Note** $V_i$ carries the subspace topology from $V$, and "bounded in $V_i$" is von Neumann boundedness of the preimage of $B$ in the subtype $V_i$.
-- source:
--   Paul Garrett, *Completeness and quasi-completeness* (lecture notes, April 24, 2014), http://www.math.umn.edu/~garrett/m/fun/notes_2012-13/07d_quasi-completeness.pdf, p. 4, Proposition 2.1.1

import Definitions.Def_GarrettFA_IsStrictColimit

namespace GarrettFA
theorem isVonNBounded_iff_of_isStrictColimit {𝕜 : Type*} [RCLike 𝕜] {V : Type*} [AddCommGroup V] [Module 𝕜 V] [Module ℝ V]
    [IsScalarTower ℝ 𝕜 V] [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousSMul 𝕜 V]
    [T2Space V] {F : ℕ → Submodule 𝕜 V} (hF : IsStrictColimit 𝕜 F)
    (B : Set V) :
    Bornology.IsVonNBounded 𝕜 B ↔
      ∃ i, B ⊆ F i ∧ Bornology.IsVonNBounded 𝕜 {y : F i | (y : V) ∈ B} := by sorry
end GarrettFA
