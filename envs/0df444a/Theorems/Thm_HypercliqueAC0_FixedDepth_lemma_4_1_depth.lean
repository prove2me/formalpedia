-- Prove2me | Theorems.Thm_HypercliqueAC0_FixedDepth_lemma_4_1_depth
-- name    : HypercliqueAC0.FixedDepth.lemma_4_1_depth
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-27T00:59:12.354804+00:00
-- url     : https://prove2.me/theorems/d0cb8083-208b-4f93-8822-a498669e62bf
-- title:
--   Lemma 4.1 with a depth bound: tracing a monomial down to a gate of no larger depth
-- statement:
--   Let $G$ be an $r$-uniform hypergraph on $[m]$, let $A\subseteq[m]$, and let $s\ge r$ be an integer. Let $C$ be a circuit on the variables $(x_e)_{e\in\binom{[m]}r}$. Suppose that some gate $\beta$ of $C$ computes a function $g$ such that the restriction $g|_{\rho_{K_A}}$ has a monomial touching more than $s$ vertices. Then there are a gate $\alpha$ of $C$, a prefix $f_{\alpha,j}$ of $\alpha$ with $j\ge1$, and sets $B_1,B_2\subseteq A$ with
--
--   $$|B_1|,|B_2|\le s<|B_1\cup B_2|$$
--
--   such that $f_{\alpha,j}$ spans $K_{B_1}\cup K_{B_2}$, and moreover the depth of $\alpha$ is at most the depth of $\beta$.
--
--   Here $\rho_H$ leaves free exactly the edges of $H$ missing in $G$ and fixes every other edge to its value in $G$, and a function spans $H$ if its restriction by $\rho_H$ has a nonzero multilinear monomial touching every vertex of $H$. This is the monomial-tracing step of the source; the depth bound replaces the source's trimming convention and is what the union bound of Lemma 4.5 needs.
--
--   **Formalization Note** Prefixes, gate values and gate depths are those of the mission's circuit interface; no assumption that every gate reaches the output is made.
-- source:
--   Chukhin, Exhaustive Search Is Hard to Beat in Constant Depth for Hyperclique and Orthogonal Vectors, STOC 2027 submission #830, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/830.pdf, §4.1, Lemma 4.1 and its proof, p.13 (PDF 15); variant without the trimming convention, recording that the traced gate lies below the starting gate.

import Mathlib
import Definitions.Def_HypercliqueAC0_FixedDepth_Planting

noncomputable section
namespace HypercliqueAC0.FixedDepth
attribute [local instance] Classical.propDecidable Classical.decEq
open scoped BigOperators

theorem lemma_4_1_depth (m r s : ℕ) (hs : r ≤ s) (G : Edge m r → Bool)
    (A : Finset (Fin m)) (C : MantriCVQ.ACCircuit (Edge m r)) (β : Fin C.gates.length)
    (hβ : hasLargeMonomial G (complete r A) (boolReal (gateValue C β)) s) :
    ∃ (α : Fin C.gates.length) (j : ℕ) (B₁ B₂ : Finset (Fin m)),
      1 ≤ j ∧ j ≤ C.gates[α.val].inputs.length ∧
      B₁ ⊆ A ∧ B₂ ⊆ A ∧ B₁.card ≤ s ∧ B₂.card ≤ s ∧ s < (B₁ ∪ B₂).card ∧
      spans G (hypergraphUnion (complete r B₁) (complete r B₂))
        (boolReal (gatePrefix C α j)) ∧
      gateDepth C α ≤ gateDepth C β := by sorry

end HypercliqueAC0.FixedDepth
