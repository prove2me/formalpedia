-- Prove2me | Theorems.Thm_Intersectionality_Generic_lemma_2
-- name    : Intersectionality.Generic.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T06:26:15.22051+00:00
-- url     : https://prove2.me/theorems/875fb76a-b732-4788-aa82-c3ff3aca36ab
-- title:
--   Lemma 2 — the set where β_𝟏 ≠ (q⁻¹_{e_n}∘⋯∘q⁻¹_{e_1})(β_𝟎) and all p(g) > 0 is open and dense in P
-- statement:
--   Let $X \subset \mathbb{R}$ be a nonempty interval, $n \ge 2$, $\alpha \in (0,1)$, and let $Q$ be a rich and commutative family of increasing bijections of $X$. For $p \in P$ write $\beta_g = F_g^{-1}(1-\alpha)$. Let $q_{e_i}$ be the unique element of $Q$ with $q_{e_i}(\beta_{e_i}) = \beta_{\mathbf 0}$, for $i = 1, \dots, n$. Then the set
--
--   $$S = \Big\{p \in P \;:\; \beta_{\mathbf 1} \ne \big(q_{e_n}^{-1} \circ \cdots \circ q_{e_1}^{-1}\big)(\beta_{\mathbf 0}) \ \text{ and } \ p(g) > 0 \text{ for all } g \in G\Big\}$$
--
--   is open and dense in $P$, with $P$ carrying the relative weak$^*$ topology.
--
--   This is the genericity step of Theorem 1(a). On $S$, the necessary condition derived from a representative nonintersectional policy fails.
--
--   **Formalization Note.** The maps $q_{e_i}$ are given by `transport`, the element of $Q$ sending $\beta_{e_i}$ to $\beta_{\mathbf 0}$. The composition is a left fold applying $q_{e_1}^{-1}$ first. Openness and density are taken in the subspace $P$, not in the space of all probability measures. The hypothesis $n \ge 2$ is the one the proof of Theorem 1 states ("For $n \ge 2$"). For $n = 1$ we have $\mathbf 1 = e_1$ and the set is empty.
-- source:
--   Carvalho, Pradelski and Williams, Intersectionality: Affirmative Action with Multidimensional Identities, hal-04788142v1, p. 23 (PDF 24), Lemma 2

import Mathlib
import Definitions.Def_Intersectionality_Generic_Setting

namespace Intersectionality.Generic

theorem lemma_2 (X : Set ℝ) (hX : X.OrdConnected) [Nonempty ↥X] (n : ℕ) (hn : 2 ≤ n)
    (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1) (Q : Set (↥X → ↥X)) (hQ : IsPolicyFamily Q) :
    let S : Set (DistSpace X n) :=
      {p | quantile p.1 α (oneGrp n) ≠
            (List.finRange n).foldl
              (fun x i => Function.invFun
                (transport Q (quantile p.1 α (unitGrp i)) (quantile p.1 α (zeroGrp n))) x)
              (quantile p.1 α (zeroGrp n)) ∧
          ∀ g, 0 < groupMass p.1 g}
    IsOpen S ∧ Dense S := by sorry

end Intersectionality.Generic
