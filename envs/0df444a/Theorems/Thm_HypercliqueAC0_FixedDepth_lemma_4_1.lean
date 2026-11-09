-- Prove2me | Theorems.Thm_HypercliqueAC0_FixedDepth_lemma_4_1
-- name    : HypercliqueAC0.FixedDepth.lemma_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T19:12:24.15052+00:00
-- url     : https://prove2.me/theorems/2f410a1d-871d-4cc8-8b8a-c324b455f309
-- title:
--   Lemma 4.1: tracing a monomial down a circuit
-- statement:
--   Let $G$ be an $r$-uniform hypergraph on $[m]$, let $A\subseteq[m]$, and let $s\ge r$ be an integer. Let $C$ be a circuit, with the standing §3.2 convention that every gate reaches the output. Suppose gate $\beta$ has a monomial touching more than $s$ vertices after restriction by $\rho_{K_A}$. Then there are a gate $\alpha$, a prefix index $1\le j\le\operatorname{fanin}(\alpha)$, and $B_1,B_2\subseteq A$ such that
--
--   $$|B_1|,|B_2|\le s<|B_1\cup B_2|,\qquad f_{\alpha,j}\text{ spans }K_{B_1}\cup K_{B_2}.$$
--
--   Moreover, if $\beta$ is not the output gate, then neither is $\alpha$. This is the deterministic tracing target; no circuit depth bound or lower bound on $r$ is added.
--
--   **Formalization Note** Gates have valid list indices and the restriction retains exactly the free edges. Isolated vertices in the union remain vertices that must be touched. The reachability hypothesis is the source's standing convention, essential for the Moreover clause, rather than a new hypothesis.
--
--   Differences from the source:
--   - encoding: $[m]=\{1,\ldots,m\}$ and $r$-subsets → $\mathrm{Fin}\,m$ with edge subtype of cardinality $r$; reason: a relabeling bijection preserves the entire hypergraph and all circuit instances
--   - encoding: the standing assumption in §3.2 that every gate lies on a path to the output → an explicit reachability predicate for Lemma 4.1; reason: the reused general circuit object does not bundle this source convention
--   - encoding: monomials of the restricted real multilinear polynomial → nonzero Möbius coefficients on the exact subtype of missing edges; reason: the verified expansion identifies these coefficients with the source polynomial
-- source:
--   Nikolai Chukhin, Exhaustive Search Is Hard to Beat in Constant Depth for Hyperclique and Orthogonal Vectors, STOC 2027 submission #830 (October 2026), source.pdf SHA-256 bd73fd887fe562527226e0ea2da24a55552a73cf89c2e90406a28965424a12de, p.13 (PDF p.15), Lemma 4.1

import Mathlib
import Definitions.Def_HypercliqueAC0_FixedDepth_Planting

noncomputable section

namespace HypercliqueAC0.FixedDepth
attribute [local instance] Classical.propDecidable Classical.decEq
open scoped BigOperators

/-- Lemma 4.1, p.13 (PDF 15). The standing §3.2 pruning convention is explicit.
There is no restriction on r, nor any depth bound. -/
theorem lemma_4_1 (m r s : ℕ) (hs : r ≤ s) (G : Edge m r → Bool)
    (A : Finset (Fin m)) (C : MantriCVQ.ACCircuit (Edge m r))
    (htrim : allGatesReachOutput C) (β : Fin C.gates.length)
    (hβ : hasLargeMonomial G (complete r A) (boolReal (gateValue C β)) s) :
    ∃ (α : Fin C.gates.length) (j : ℕ) (B₁ B₂ : Finset (Fin m)),
      1 ≤ j ∧ j ≤ C.gates[α.val].inputs.length ∧
      B₁ ⊆ A ∧ B₂ ⊆ A ∧ B₁.card ≤ s ∧ B₂.card ≤ s ∧ s < (B₁ ∪ B₂).card ∧
      spans G (hypergraphUnion (complete r B₁) (complete r B₂))
        (boolReal (gatePrefix C α j)) ∧
      (¬ isOutputGate C β → ¬ isOutputGate C α) := by sorry

end HypercliqueAC0.FixedDepth
