-- Prove2me | Theorems.Thm_MultStretchAPASP_Weighted_theorem_2_14
-- name    : MultStretchAPASP.Weighted.theorem_2_14
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T07:10:58.908523+00:00
-- url     : https://prove2.me/theorems/15f3c742-d0a3-44a4-944f-e48a174672b9
-- title:
--   Theorem 2.14 (Elkin–Neiman) — deterministic (1 + ε)-MSASP in Õ(m^{1+o(1)} + (1/ε)^{O(1)} n^{ω(1,r,1)+o(1)})
-- statement:
--   Let $G=(V,E,w)$ be an undirected graph with $n$ vertices and $m$ edges and $S\subseteq V$ a set of sources with $|S|=O(n^r)$ for some $r>0$. For every $\varepsilon>0$ there is a deterministic algorithm that computes $(1+\varepsilon)$-MSASP for $S\times V$, i.e. values $\bar\delta(s,v)$ with $\delta(s,v)\le\bar\delta(s,v)\le(1+\varepsilon)\delta(s,v)$, in time
--   $$\tilde O\Bigl(m^{1+o(1)}+\bigl(\tfrac1\varepsilon\bigr)^{O(1)}\,n^{\omega(1,r,1)+o(1)}\Bigr).$$
--
--   Formally: for every $r>0$, every $C_0$ (with $|S|\le C_0n^r$) and every $\eta>0$ there is $C$ such that for every $\varepsilon>0$ some deterministic program halts on every such input within $C(\log_2(n+2))^C\bigl(m^{1+\eta}+(1+1/\varepsilon)^C n^{\omega(1,r,1)+\eta}\bigr)+C$ steps with a correct output. Algorithm 10 uses it in line 10 with $S=S_1$.
--
--   Differences from the source:
--
--   - reading: an algorithm with a running time (the paper names no machine model) → a program of the published randomized word RAM DynConnWC.Program with the run notions of MinKCutII_Main_Runs, words of wordSize C inp T = C·⌈log₂(|inp| + Σ inp + 2 + ⌈T⌉)⌉ bits, input read once in order, output written as words; reason: a standard unit-cost word RAM with Θ(log)-bit words; the same machine defines ω(a, b, c), so the exponents in the bounds and the machine agree
--   - reading: a weighted undirected graph with weights in ℝ≥0 → a simple graph given as edge records with non-negative integer weights (SimpleEdges), read as input words; reason: a word RAM takes integer inputs; the paper's graphs are simple
--   - encoding: a vertex set V with |V| = n → Fin n with 1 ≤ n; reason: a fixed vertex type; n ≥ 1 makes log n and n^(−c) meaningful
--   - reading: |S| = O(n^r) → |S| ≤ C₀·n^r with C₀ quantified before the constants; reason: the O-constant is fixed before the algorithm's constants
--   - reading: Õ(m^{1+o(1)} + (1/ε)^{O(1)} n^{ω(1,r,1)+o(1)}) → for every η > 0 one constant C, uniform in ε, and for every ε > 0 a program with time C·(log₂(n+2))^C·(m^{1+η} + (1 + 1/ε)^C·n^{ω(1,r,1)+η}) + C; reason: (1/ε)^{O(1)} is meaningful only with a constant independent of ε; 1 + 1/ε is within a factor 2 of 1/ε for ε ≤ 1 and also covers ε > 1
--   - encoding: (1 + ε)-MSASP for S × V → the output lists, for the sources in increasing order, the natural-number (or ∞) values δ̄(s, v) in the two-word code, with δ(s, v) ≤ δ̄(s, v) ≤ (1 + ε)δ(s, v); reason: distances are integers, so the floor of any admissible estimate is admissible; ∞ needs an unambiguous code
--   - reading: ω(a, b, c): "the infimum over all τ > 0 such that, for every constant ε > 0, the product A·B can be computed in O(n^{τ+ε}) runtime" (p. 7), A ∈ ℝ^{n^a×n^b}, B ∈ ℝ^{n^b×n^c}; ω = ω(1, 1, 1) → omega3 a b c: the infimum of the τ > 0 achievable, for every ε > 0, by a deterministic program of the word RAM of DynConnWC_Program in C·N^{τ+ε} + C steps on natural-number matrices of sizes ⌈N^a⌉ × ⌈N^b⌉ and ⌈N^b⌉ × ⌈N^c⌉; omega = omega3 1 1 1; reason: the paper defines ω by running time and names no machine; a word RAM takes integer inputs; deterministic because Theorem 2.14 claims a deterministic algorithm in time n^{ω(1,r,1)+o(1)}; the same machine runs every algorithm of the mission
-- source:
--   Saggi, Sapir, Smallest Multiplicative Stretch for an α-APASP Below Õ(n^ω) Runtime, arXiv:2611.04736 (version of November 3, 2026, sha256 7cbb8123…), p. 7, Theorem 2.14

import Mathlib
import Definitions.Def_DynConnWC_Program
import Definitions.Def_MinKCutII_Main_Runs
import Definitions.Def_MultStretchAPASP_Weighted_Graph
import Definitions.Def_MultStretchAPASP_Weighted_MinPlus
import Definitions.Def_MultStretchAPASP_Weighted_Encoding
import Definitions.Def_MultStretchAPASP_Weighted_OmegaExp

set_option autoImplicit false

open DynConnWC MinKCutII.Main

namespace MultStretchAPASP.Weighted

/-- **Theorem 2.14** (p. 7; Theorem 5 of Elkin–Neiman [14]). For every `r > 0` and every constant
`C₀` (the sources satisfy `|S| ≤ C₀·n^r`, i.e. `|S| = O(n^r)`) and every `η > 0` (the `o(1)`
terms) there is a constant `C` such that for every `ε > 0` there is a deterministic program that,
on every simple undirected graph on `n ≥ 1` vertices with `m` edges of non-negative integer
weight and every such source set `S`, halts within
`C·(log₂(n+2))^C·(m^{1+η} + (1 + 1/ε)^C·n^{ω(1,r,1)+η}) + C` steps and outputs a
`(1 + ε)`-MSASP table for `S × V`: `δ(s, v) ≤ δ̄(s, v) ≤ (1 + ε)·δ(s, v)`. -/
theorem theorem_2_14 :
    ∀ r : ℝ, 0 < r → ∀ C₀ : ℝ, ∀ η : ℝ, 0 < η → ∃ C : ℕ, ∀ ε : ℝ, 0 < ε →
      ∃ P : Program, IsDeterministic P ∧
        ∀ (n : ℕ) (es : List (Fin n × Fin n × ℕ)) (S : Finset (Fin n)), 1 ≤ n → SimpleEdges es →
          (S.card : ℝ) ≤ C₀ * (n : ℝ) ^ r →
          let T : ℝ := (C : ℝ) * polylog n C *
            ((es.length : ℝ) ^ (1 + η) + (1 + 1 / ε) ^ C * (n : ℝ) ^ (omega3 1 r 1 + η)) + C
          let inp := msaspInput es S
          let W := wordSize C inp T
          ∀ ω : ℕ → Fin (2 ^ W),
            HaltsWithin W P inp ω T ∧ IsMSASPOutput (ofEdges es) S ε (finalOutput W P inp ω) := by sorry

end MultStretchAPASP.Weighted
