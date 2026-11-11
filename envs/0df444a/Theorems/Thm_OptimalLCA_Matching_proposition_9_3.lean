-- Prove2me | Theorems.Thm_OptimalLCA_Matching_proposition_9_3
-- name    : OptimalLCA.Matching.proposition_9_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T15:47:58.901508+00:00
-- url     : https://prove2.me/theorems/0011408d-bff7-4d30-be41-6a5d8f468aef
-- title:
--   Proposition 9.3 — local degree halving: H_J is a matching, E|E(H_J)| ≥ (1 − ξ)|E(H₀)|/D, mate cost A(CDR²)^J
-- statement:
--   Let $D=2K=2^J$ ($J\ge1$), $0<\xi<\tfrac12$, $p=\xi/(2J)$, $R=\lceil2\log(1/p)/p\rceil$, and $H_0=B(H)$ for a kept-proposal multigraph $H$ of maximum degree at most $D$, with lifted IDs ordered lexicographically and i.i.d. $\mathrm{Bern}(p)$ marks per original ID and level, shared by both lifts. After $J$ halving steps $H_J$ is a matching (for every choice of marks) and
--   $$\mathbb E\big[|E(H_J)|\,\big|\,H_0\big]\ge\frac{(1-\xi)|E(H_0)|}D.$$
--   There is an absolute constant $C$ such that one program answers mate queries to $H_J$ using the ID-sorted incident lists of $H_0$ and the marks: if a list costs at most $A$ total work, a mate query costs at most $A(CDR^2)^J$ total work. Answers are determined by the fixed IDs, the marks and the query, so they are consistent in every query order.
--
--   Differences from the source:
--   - generalization: H₀ = B(H) for the kept-proposal multigraph H of §7.2 (D = 2K) → H₀ = B(H) for any kept-proposal multigraph H on Fin n with IDs Fin n × Fin K, no loops, maximum degree ≤ D; reason: the §7.2 multigraph is such an H, so the item specializes to the source; the proof uses only these properties
--   - reading: E[|E(H_J)| | H₀] → the expectation over the marks for every fixed H; reason: H₀ is a function of H; the marks are independent of the proposal seeds
--   - reading: if a sorted list of copies at a vertex of H₀ costs at most A total work, a mate query costs at most A(CDR²)^J total work → a list oracle charged A per call, every other instruction 1; (other instructions) + A·(list calls) ≤ A(C·2^J·R²)^J, for every A ≥ 1, one program for all H, marks, queries; reason: the list is an oracle in the proposition; its cost is the parameter A
--   - reading: the same bound therefore holds for graph queries and arithmetic operations → not a separate clause: arithmetic operations are counted in the work; graph queries occur only inside the list oracle; reason: a consequence of the work bound once lists are implemented
--   - encoding: mate of a vertex of H₀, ⊥ when unmatched; sides {1, 2} → output 2w + s′ for the mate (w, s′), −1 for ⊥; sides Fin 2; reason: machine output register
-- source:
--   Cohen, Roghani, Optimal LCA and Sublinear Estimation for Bipartite Matching in Δ^O(1/ε) Queries, arXiv:2611.06024 (version not printed; PDF sha256 5a43ec12…3eb3), p. 44, Proposition 9.3

import Mathlib
import Definitions.Def_OptimalLCA_Matching_Machine
import Definitions.Def_OptimalLCA_Matching_DegreeHalving

namespace OptimalLCA.Matching

/-- Proposition 9.3 (local degree halving). Let `D = 2K = 2^J`, `0 < ξ < 1/2`,
`p = ξ/(2J)`, `R = ⌈2 log(1/p)/p⌉`, and `H₀ = B(H)` for a kept-proposal multigraph `H` of
maximum degree at most `D`. After `J` steps `H_J` is a matching, and
`E[|E(H_J)| | H₀] ≥ (1 - ξ)|E(H₀)|/D` for i.i.d. `Bern(p)` marks per original ID and level.
There is an absolute constant `C` such that one program answers mate queries to `H_J`
from the ID-sorted incident lists of `H₀` and the marks; if a list costs at most `A`, a
mate query costs at most `A (C D R²)^J` total work. Answers are functions of the IDs, the
marks and the query, hence consistent in every query order. -/
theorem proposition_9_3 :
    ∃ C : ℝ, 0 < C ∧
    ∀ K J : ℕ, 1 ≤ J → 2 * K = 2 ^ J → ∀ ξ : ℝ, 0 < ξ → ξ < 1 / 2 →
      (∀ (n : ℕ) (H : KeptMultigraph n K), H.MaxDegLE (2 ^ J) →
        (∀ (marks : ℕ → Fin n × Fin K → Bool) (x : Fin n × Fin 2),
          ((halvingSeq H marks (rParam ξ J) J).filter (fun c => x ∈ liftEnds H c)).card ≤ 1) ∧
        (1 - ξ) * ((liftAll H).card : ℝ) / (2 ^ J : ℝ) ≤ expectedFinal H J ξ) ∧
      ∃ P : Program, ∀ (n : ℕ) (H : KeptMultigraph n K), H.MaxDegLE (2 ^ J) →
        ∀ (marks : ℕ → Fin n × Fin K → Bool) (x : Fin n × Fin 2) (A : ℝ), 1 ≤ A →
          HaltsWithinListCost P (halvingEnv H marks) (halvingInput x) A
              (A * (C * (2 ^ J : ℝ) * (rParam ξ J : ℝ) ^ 2) ^ J) ∧
          (∀ c ∈ halvingSeq H marks (rParam ξ J) J, x ∈ liftEnds H c →
            ∀ y ∈ liftEnds H c, y ≠ x →
              output P (halvingEnv H marks) (halvingInput x) =
                some (2 * (y.1.val : ℝ) + (y.2.val : ℝ))) ∧
          ((∀ c ∈ halvingSeq H marks (rParam ξ J) J, x ∉ liftEnds H c) →
            output P (halvingEnv H marks) (halvingInput x) = some (-1)) := by sorry

end OptimalLCA.Matching
