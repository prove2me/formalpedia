-- Prove2me | Theorems.Thm_LogStarBinPacking_lemma_3_3
-- name    : LogStarBinPacking.lemma_3_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T01:32:30.575434+00:00
-- url     : https://prove2.me/theorems/29b7210f-cc03-4235-ae8e-923bbb2579d9
-- title:
--   Lemma 3.3 — $c(n)=\Theta(\log^*n)$ keeps $A$ uniformly polynomial
-- statement:
--   There is a computable integer function $c(n)=\Theta(\log^*n)$, defined for all sufficiently large $n$, such that for every simple graph $G$ with $n$ vertices and at least one edge and every integer $0\le k\le n$, the algorithm $A$ of Proposition 3.1 on input $(G,k,c(n))$ with the parameters (3.1) runs in uniform deterministic polynomial time. Its output has
--   $$
--   N=O(n^5)
--   $$
--   items per class, each with $O(n^2\log n)$ bits.
--
--   This is what makes the additive gap grow with the input while the reduction stays polynomial.
--
--   **Formalization Note** $\Theta$ and $O$ are explicit constants $a,b>0$, $C$ and a threshold $n_0$, chosen before $G$ and $k$. One machine computes the output of $A$ on all inputs with $n\ge n_0$; the parameters (3.1) are those of the published construction at $\rho=1/96$ ($d=11520K$).
--
--   Differences from the source:
--   - reading: c(n) = Θ(log∗ n), N = O(n⁵), O(n² log n) bits → a·log∗n ≤ c(n) ≤ b·log∗n, N ≤ C·n⁵, bits ≤ C·n²·log n for n ≥ n₀, with a, b > 0, C, n₀ chosen before G, k; reason: the asymptotic notation of the statement; the constants are absolute
--   - encoding: c defined for all sufficiently large n → a total Computable c : ℕ → ℕ whose values below n₀ are unused; the machine's values below n₀ are unused; reason: the statement only concerns large n
--   - encoding: "runs in uniform deterministic polynomial time" → one TM2ComputableInPolyTime machine with a finite alphabet, from graphBits, equal to fiveClassOutput (c n) (1/96) for n ≥ n₀; reason: one machine for all n is the uniformity
--   - encoding: the width D∗ = Z of Lemma 3.2 in the denominator (3.6) → the published construction's own width bound (geometryBound, the largest child label); reason: A is the published construction; (3.7) holds for either bound
--   - encoding: the bit length of an item → size p + size q for the item p/q; reason: binary length of numerator and denominator
-- source:
--   I. Doron-Arad, Additive Ω(log∗ OPT) Gap for Bin Packing with Three Items per Bin, manuscript (sha256 1d88425d…), Lemma 3.3, p.15; (3.1), p.12

import Mathlib
import Definitions.Def_BinPackingGap
import Definitions.Def_OAIQ082C014
import Definitions.Def_PacketRouting_CongDil_Recurrences
import Definitions.Def_LogStarBinPacking_FiveClassRaw
import Definitions.Def_LogStarBinPacking_fiveClassOutput

namespace LogStarBinPacking

open OAI.BinPackingGap OAI.BinPackingGames.Foundations.Complexity

/-- **Lemma 3.3 (the gap can grow).** Doron-Arad, *Additive Ω(log∗ OPT) Gap for Bin Packing with Three Items per Bin*, manuscript (sha256 1d88425d…), Lemma 3.3, p.15 (parameters (3.1), p.12).
There is a computable integer function `c(n) = Θ(log∗ n)`, defined for all sufficiently large
`n`, such that for every simple graph `G` with `n` vertices and at least one edge and every
integer `0 ≤ k ≤ n`, the algorithm `A` of Proposition 3.1, on input `(G, k, c(n))` with
parameters (3.1), runs in uniform deterministic polynomial time. Its output has `N = O(n⁵)` items
per class, each with `O(n² log n)` bits.

**Formalization Note** `c` is a total `Computable` function; its values below `n₀` are not
used. `Θ(log∗ n)` is `a·log∗ n ≤ c(n) ≤ b·log∗ n` for `n ≥ n₀` with `a, b > 0`. One machine
`f` (Mathlib `TM2ComputableInPolyTime`, finite alphabet, from `graphBits`) computes the output
`fiveClassOutput (c n) (1/96) x` of `A` on every input with `n ≥ n₀` vertices; its values below
`n₀` are not used. The published construction at `ρ = 1/96` uses the parameters (3.1)
(`depthDemand c (1/96) = 11520K = d`). An item `(p, q)` (size `p/q`) has `size p + size q` bits.
All `O(·)` constants are absolute, chosen before `G` and `k`. -/
theorem lemma_3_3 :
    ∃ c : ℕ → ℕ, Computable c ∧
    ∃ a b : ℝ, 0 < a ∧ 0 < b ∧ ∃ n₀ : ℕ, ∃ C : ℝ,
    ∃ f : GraphReductionInput → FiveClassRaw,
    ∃ comp : Turing.TM2ComputableInPolyTime graphBits FiveClassRaw.bits f,
      MachineFiniteAlphabet.FiniteAlphabet comp.tm ∧
      (∀ n : ℕ, n₀ ≤ n →
        a * (PacketRouting.CongDil.logStar (n : ℝ) : ℝ) ≤ (c n : ℝ) ∧
        (c n : ℝ) ≤ b * (PacketRouting.CongDil.logStar (n : ℝ) : ℝ)) ∧
      ∀ x : GraphReductionInput, n₀ ≤ x.graph.n →
        f x = fiveClassOutput (c x.graph.n) (1 / 96) x ∧
        ((f x).1 : ℝ) ≤ C * (x.graph.n : ℝ) ^ 5 ∧
        ∀ cl ∈ (f x).2, ∀ q ∈ cl,
          ((Nat.size q.1 + Nat.size q.2 : ℕ) : ℝ) ≤
            C * (x.graph.n : ℝ) ^ 2 * Real.log (x.graph.n : ℝ) := by sorry

end LogStarBinPacking
