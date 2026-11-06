-- Prove2me | Theorems.Thm_LogStarBinPacking_lemma_4_1
-- name    : LogStarBinPacking.lemma_4_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T01:29:48.624566+00:00
-- url     : https://prove2.me/theorems/a1aab468-ecc7-4572-be7d-6b8afd282d82
-- title:
--   Lemma 4.1 — NP-hardness of $\tau(G)=2n/3$ versus $\tau(G)\ge2n/3+n/48$
-- statement:
--   For simple graphs $G$ with $n=|V(G)|$ divisible by three, it is NP-hard to distinguish the cases
--   $$
--   \text{(i)}\ \ \tau(G)=\frac{2n}3,\qquad\qquad \text{(ii)}\ \ \tau(G)\ge\frac{2n}3+\frac n{48}.
--   $$
--   Moreover, by taking a fixed number of disjoint copies, the graphs can be required to have more than any prescribed number of vertices.
--
--   This vertex-cover gap with an exact YES value feeds Proposition 3.1 with $k=2n/3$ in the proof of Theorem 1.1.
--
--   **Formalization Note** NP-hardness: for every $n_0$ and every language $L$ in NP there is a polynomial-time map (finite-alphabet Turing machine) from words to explicit simple graphs with $n\ge n_0$, $n\ge1$ and $3\mid n$, landing in (i) on members of $L$ and in (ii) on non-members. Case (i) is $3\tau=2n$; case (ii) is compared in $\mathbb R$.
--
--   Differences from the source:
--   - reading: "it is NP-hard to distinguish" → every InNP language has a polynomial-time finite-alphabet reduction to explicit graphs landing in (i) on members and (ii) on non-members; reason: the standard Karp reading of a promise problem's NP-hardness, as in the published PackingGapNPHard
--   - generalization: n divisible by three → also n ≥ n₀ for every prescribed n₀, and n ≥ 1; reason: outputs are restricted further, so the statement implies the source's; the padding is the last sentence of the proof, used for Theorem 1.1
--   - encoding: 2n/3 and n/48 → (i) as 3τ = 2n in ℕ, (ii) in ℝ; reason: exact arithmetic, no natural-number division
-- source:
--   I. Doron-Arad, Additive Ω(log∗ OPT) Gap for Bin Packing with Three Items per Bin, manuscript (sha256 1d88425d…), Lemma 4.1 and the last sentence of its proof, pp.16–17

import Mathlib
import Definitions.Def_BinPackingGap
import Definitions.Def_VertexCover

namespace LogStarBinPacking

open OAI.BinPackingGap OAI.BinPackingGames.Foundations.Complexity

/-- **Lemma 4.1 (vertex-cover gap).** Doron-Arad, *Additive Ω(log∗ OPT) Gap for Bin Packing with Three Items per Bin*, manuscript (sha256 1d88425d…), Lemma 4.1, p.16 (and the last sentence of its proof,
p.17). For simple graphs `G` with `n = |V(G)|` divisible by three, it is NP-hard to distinguish
the following two cases: (i) `τ(G) = 2n/3`; (ii) `τ(G) ≥ 2n/3 + n/48`.

**Formalization Note** NP-hardness of the promise problem: for every language `L` in NP there is
a polynomial-time map (Mathlib `TM2ComputableInPolyTime`, finite alphabet) from words to explicit
simple graphs (`ExplicitGraph`, encoded by `ExplicitGraph.bits`) whose output always has `n`
divisible by three and `n ≥ 1`, lands in case (i) when `x ∈ L` and in case (ii) when `x ∉ L`.
The lower bound `n₀ ≤ n`, for every `n₀`, is the padding of the proof's last sentence ("taking a
fixed number of disjoint copies … makes `n` exceed any prescribed constant"). `τ` is
`coverNumber`; (i) is `3τ = 2n`, (ii) is compared in `ℝ`. -/
theorem lemma_4_1 :
    ∀ n₀ : ℕ, ∀ L : BitLanguage, CookLevin.InNP L →
    ∃ construct : List Bool → OAI.VertexCover.ExplicitGraph,
    ∃ comp : Turing.TM2ComputableInPolyTime (id : List Bool → List Bool)
        OAI.VertexCover.ExplicitGraph.bits construct,
      MachineFiniteAlphabet.FiniteAlphabet comp.tm ∧
      ∀ x : List Bool,
        n₀ ≤ (construct x).n ∧ 1 ≤ (construct x).n ∧ 3 ∣ (construct x).n ∧
        (L x → 3 * (construct x).coverNumber = 2 * (construct x).n) ∧
        (¬ L x → 2 * ((construct x).n : ℝ) / 3 + ((construct x).n : ℝ) / 48 ≤
          ((construct x).coverNumber : ℝ)) := by sorry

end LogStarBinPacking
