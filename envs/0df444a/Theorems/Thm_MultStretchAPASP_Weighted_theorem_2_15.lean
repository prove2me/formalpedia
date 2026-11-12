-- Prove2me | Theorems.Thm_MultStretchAPASP_Weighted_theorem_2_15
-- name    : MultStretchAPASP.Weighted.theorem_2_15
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T07:11:07.430193+00:00
-- url     : https://prove2.me/theorems/8d76e177-1faa-439b-bd5c-9e5fffae985c
-- title:
--   Theorem 2.15 (Zwick, rectangular) — (1 + ε)-approximate (min, +)-product of n × n^r and n^r × n matrices in Õ((1/ε) n^{ω(1,r,1)+o(1)} log W_max)
-- statement:
--   Let $r\in[0,1]$ and let $A$, $B$ be matrices of dimensions $n\times n^r$ and $n^r\times n$ with entries in $\{0\}\cup[W_{\max}]\cup\{\infty\}$. For every $\varepsilon>0$ there is an algorithm that computes an entrywise $(1+\varepsilon)$-approximation $M$ of $A\star B$, i.e. $(A\star B)[i,j]\le M[i,j]\le(1+\varepsilon)(A\star B)[i,j]$, in time
--   $$\tilde O\Bigl(\tfrac1\varepsilon\cdot n^{\omega(1,r,1)+o(1)}\cdot\log W_{\max}\Bigr).$$
--
--   Formally: for every $r\in[0,1]$ and $\eta>0$ there is $C$ such that for every $\varepsilon>0$ some program, for all $n\ge1$, $W_{\max}\ge1$ and such matrices, halts on every random tape within $C(\log_2(n+2))^C(1+1/\varepsilon)\,n^{\omega(1,r,1)+\eta}\,L+C$ steps, $L=\log_2(W_{\max}+1)+1$, with a correct output. Algorithm 10 uses it in line 11 and inside Algorithm 9.
--
--   Differences from the source:
--
--   - reading: an algorithm with a running time (the paper names no machine model) → a program of the published randomized word RAM DynConnWC.Program with the run notions of MinKCutII_Main_Runs, words of wordSize C inp T = C·⌈log₂(|inp| + Σ inp + 2 + ⌈T⌉)⌉ bits, input read once in order, output written as words; reason: a standard unit-cost word RAM with Θ(log)-bit words; the same machine defines ω(a, b, c), so the exponents in the bounds and the machine agree
--   - encoding: dimensions n × n^r and n^r × n → Fin n × Fin ⌈n^r⌉ and Fin ⌈n^r⌉ × Fin n, n ≥ 1; reason: n^r rounded up to an integer dimension
--   - encoding: entries in {0} ∪ [W_max] ∪ {∞} → entries in ℕ∞ that are ≤ Wmax or ⊤, with 1 ≤ Wmax; input [n, ⌈n^r⌉, n, Wmax, 0, 0] followed by both matrices in the two-word code; reason: [W_max] is nonempty only for W_max ≥ 1; ∞ needs an unambiguous code
--   - reading: an algorithm which computes … in time T → a program that on every random tape halts within T steps with a correct output; reason: the strong worst-case reading
--   - reading: Õ((1/ε) n^{ω(1,r,1)+o(1)} log W_max) → for every η > 0 one constant C, uniform in ε, and for every ε > 0 a program with time C·(log₂(n+2))^C·(1 + 1/ε)·n^{ω(1,r,1)+η}·(log₂(Wmax+1) + 1) + C; reason: the explicit 1/ε factor is meaningful only with a constant independent of ε; 1 + 1/ε is within a factor 2 of 1/ε for ε ≤ 1 and also covers ε > 1
--   - encoding: an entrywise (1 + ε)-approximation M → M with entries in ℕ∞ written in the two-word code; reason: the product has integer entries, so the floor of any admissible approximation is admissible
--   - reading: ω(a, b, c): "the infimum over all τ > 0 such that, for every constant ε > 0, the product A·B can be computed in O(n^{τ+ε}) runtime" (p. 7), A ∈ ℝ^{n^a×n^b}, B ∈ ℝ^{n^b×n^c}; ω = ω(1, 1, 1) → omega3 a b c: the infimum of the τ > 0 achievable, for every ε > 0, by a deterministic program of the word RAM of DynConnWC_Program in C·N^{τ+ε} + C steps on natural-number matrices of sizes ⌈N^a⌉ × ⌈N^b⌉ and ⌈N^b⌉ × ⌈N^c⌉; omega = omega3 1 1 1; reason: the paper defines ω by running time and names no machine; a word RAM takes integer inputs; deterministic because Theorem 2.14 claims a deterministic algorithm in time n^{ω(1,r,1)+o(1)}; the same machine runs every algorithm of the mission
-- source:
--   Saggi, Sapir, Smallest Multiplicative Stretch for an α-APASP Below Õ(n^ω) Runtime, arXiv:2611.04736 (version of November 3, 2026, sha256 7cbb8123…), p. 7, Theorem 2.15

import Mathlib
import Definitions.Def_DynConnWC_Program
import Definitions.Def_MinKCutII_Main_Runs
import Definitions.Def_MultStretchAPASP_Weighted_Graph
import Definitions.Def_MultStretchAPASP_Weighted_MinPlus
import Definitions.Def_MultStretchAPASP_Weighted_Encoding
import Definitions.Def_MultStretchAPASP_Weighted_OmegaExp

set_option autoImplicit false

open scoped ENNReal
open DynConnWC MinKCutII.Main

namespace MultStretchAPASP.Weighted

/-- **Theorem 2.15** (p. 7; rectangular version of Lemma 8.1 of Zwick [30]). For every
`r ∈ [0, 1]` and `η > 0` (the `o(1)`) there is a constant `C` such that for every `ε > 0` there is
a program that, for all `n ≥ 1`, `Wmax ≥ 1` and matrices `A` (`n × ⌈n^r⌉`) and `B`
(`⌈n^r⌉ × n`) with entries in `{0} ∪ [Wmax] ∪ {∞}`, on every random tape halts within
`C·(log₂(n+2))^C·(1 + 1/ε)·n^{ω(1,r,1)+η}·(log₂(Wmax+1) + 1) + C` steps and outputs an entrywise
`(1 + ε)`-approximation of `A ⋆ B`. -/
theorem theorem_2_15 :
    ∀ r : ℝ, 0 ≤ r → r ≤ 1 → ∀ η : ℝ, 0 < η → ∃ C : ℕ, ∀ ε : ℝ, 0 < ε → ∃ P : Program,
      ∀ (n Wmax : ℕ) (A : Fin n → Fin (dimOf n r) → ℕ∞) (B : Fin (dimOf n r) → Fin n → ℕ∞),
        1 ≤ n → 1 ≤ Wmax →
        (∀ i k, A i k ≤ (Wmax : ℕ∞) ∨ A i k = ⊤) → (∀ k j, B k j ≤ (Wmax : ℕ∞) ∨ B k j = ⊤) →
        let T : ℝ := (C : ℝ) * polylog n C *
          ((1 + 1 / ε) * (n : ℝ) ^ (omega3 1 r 1 + η) * logW Wmax) + C
        let inp := minPlusInput Wmax 0 0 A B
        let W := wordSize C inp T
        ∀ ω : ℕ → Fin (2 ^ W), HaltsWithin W P inp ω T ∧
          ∃ M : Fin n → Fin n → ℕ∞, finalOutput W P inp ω = rowsWords (List.finRange n) M ∧
            IsApproxMinPlus ε Finset.univ Finset.univ Finset.univ
              (fun i k => (A i k : ℝ≥0∞)) (fun k j => (B k j : ℝ≥0∞)) (fun i j => (M i j : ℝ≥0∞)) := by sorry

end MultStretchAPASP.Weighted
