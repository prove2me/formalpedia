-- Prove2me | Theorems.Thm_HDXNbhdPCP_Main_theorem_1_1
-- name    : HDXNbhdPCP.Main.theorem_1_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T01:00:07.13249+00:00
-- url     : https://prove2.me/theorems/f0e54b2b-26a5-48b3-a09f-93726055abe6
-- title:
--   Theorem 1.1 — NP-hardness of projection Label Cover with size $n(\log n)^C$, alphabet $\exp((1/\varepsilon)^C)$, soundness $\varepsilon>(\log n)^{-a}$
-- statement:
--   A **projection Label Cover instance** $I$ consists of a bipartite graph $(L,R,E)$, finite alphabets $\Sigma_L,\Sigma_R$ and a projection $P_e:\Sigma_L\to\Sigma_R$ for every edge $e$; its value $\mathrm{val}(I)$ is the largest fraction of edges $e=(\ell,r)$ with $P_e(a_\ell)=b_r$ over all labellings $a,b$, its size is $|L|+|R|+|E|$ and its alphabet size $\max(|\Sigma_L|,|\Sigma_R|)$ (Definition 7.1). A **3-colouring instance** is a finite simple graph $G$, of size $n=|V(G)|+|E(G)|$.
--
--   There are absolute constants $a,C>0$, a threshold $n_0$ and one polynomial-time algorithm $R$, which receives a graph $G$ and a rational $\varepsilon$ and outputs a projection Label Cover instance $I=R(G,\varepsilon)$, such that for every $G$ of size $n\ge n_0$ and every $\varepsilon>(\log n)^{-a}$:
--
--   1. $|L|+|R|+|E|\le n(\log n)^C$ and $\max(|\Sigma_L|,|\Sigma_R|)\le\exp\big((1/\varepsilon)^C\big)$;
--   2. **completeness:** if $G$ is 3-colourable then $\mathrm{val}(I)=1$;
--   3. **soundness:** if $G$ is not 3-colourable then $\mathrm{val}(I)\le\varepsilon$.
--
--   In symbols,
--   $$G\in3\text{-COL}\Rightarrow\mathrm{val}(R(G,\varepsilon))=1,\qquad G\notin3\text{-COL}\Rightarrow\mathrm{val}(R(G,\varepsilon))\le\varepsilon,\qquad \varepsilon>(\log n)^{-a}.$$
--
--   Equivalently, two-query PCPs for NP of length $n\,\mathrm{polylog}\,n$, alphabet $\exp(\mathrm{poly}(1/\varepsilon))$ and soundness $\varepsilon$ down to inverse polylogarithmic.
--
--   **Formalization Note** Polynomial time is Mathlib's `Turing.TM2ComputableInPolyTime` with the input encoding `encodeGraphEps` (graph in unary/adjacency matrix, $\varepsilon$ in binary) and the published `encodeLabelCover`; the polynomial is fixed before $\varepsilon$. The value is `FourToOneGames.LabelCover.val`, the supremum over labellings of the fraction of satisfied edges, which is $0$ on an instance with no edge (and when no labelling exists). The alphabet bound is stated as $|\Sigma_L|,|\Sigma_R|\le\lfloor\exp((1/\varepsilon)^C)\rfloor$, equivalent for integers. The printed statement puts no upper bound on $\varepsilon$; see the insights of this mission.
--
--   Differences from the source:
--   - reading: 'for every sufficiently large n and every ε > (log n)^{-a}, there is a polynomial-time reduction' → one function R(G, ε) with ε part of the input and one polynomial-time machine, the polynomial fixed before ε; reason: the uniform reading is the stronger one; a per-ε or per-n machine would be weaker
--   - reading: the size n of a 3-coloring instance (not defined) → n = |V(G)| + |E(G)|; reason: the same measure Definition 7.1 uses for Label Cover; polynomially related to every standard encoding length
--   - encoding: log → natural logarithm Real.log; reason: a, C and n₀ are existential, so any fixed base gives an equivalent statement
--   - encoding: a 3-coloring instance; a projection Label Cover instance; polynomial time → SimpleGraph (Fin k) with G.Colorable 3; FourToOneGames.LabelCover; TM2ComputableInPolyTime encodeGraphEps encodeLabelCover; reason: explicit encodings of the same objects
--   - encoding: val(I) (undefined for an instance without edges) → FourToOneGames.LabelCover.val, which is 0 there; reason: the published definition's convention; it only affects degenerate outputs
--   - encoding: alphabet size at most exp((1/ε)^C) → AlphabetBound ⌊exp((1/ε)^C)⌋₊ (both alphabets); reason: alphabet sizes are natural numbers
--   - encoding: every real ε > (log n)^{-a} → every rational ε > (log n)^{-a} (ε is an input of the machine); reason: a real ε follows from a rational ε′ < ε close enough to it: val ≤ ε′ < ε, ε′ > (log n)^{-a}, and ⌊exp((1/ε′)^C)⌋ = ⌊exp((1/ε)^C)⌋ by continuity from above
-- source:
--   Dikstein, Dinur, Hopkins, Singer, Sounder, shorter, and simpler PCPs from HDX neighborhoods, STOC 2027 submission (manuscript sha256 7dcb1b53…), p. 4, Theorem 1.1 (Definition 7.1, p. 46; proof §7, pp. 47-51)

import Mathlib
import Definitions.Def_FourToOneGames_LabelCover
import Definitions.Def_HDXNbhdPCP_Main_Encoding

open FourToOneGames

namespace HDXNbhdPCP.Main

/-- Theorem 1.1 (PCPs from neighbourhood agreement): one polynomial-time reduction `R`, taking a
graph `G` and a rational `ε`, such that for every `G` of size `n = |V| + |E| ≥ n₀` and every
`ε > (log n)^{-a}` the projection Label Cover instance `R(G, ε)` has size at most `n (log n)^C`,
alphabet size at most `exp((1/ε)^C)`, value `1` if `G` is 3-colourable and value at most `ε`
otherwise. -/
theorem theorem_1_1 :
    ∃ a C : ℝ, 0 < a ∧ 0 < C ∧ ∃ n₀ : ℕ,
    ∃ R : GraphEpsInput → LabelCover,
      Nonempty (Turing.TM2ComputableInPolyTime encodeGraphEps encodeLabelCover R) ∧
      ∀ (k : ℕ) (G : SimpleGraph (Fin k)) (ε : ℚ),
        n₀ ≤ graphSize G → Real.log (graphSize G) ^ (-a) < (ε : ℝ) →
        ((R (⟨k, G⟩, ε)).nL + (R (⟨k, G⟩, ε)).nR + (R (⟨k, G⟩, ε)).edges.card : ℝ) ≤
            graphSize G * Real.log (graphSize G) ^ C ∧
        (R (⟨k, G⟩, ε)).AlphabetBound ⌊Real.exp ((1 / (ε : ℝ)) ^ C)⌋₊ ∧
        (G.Colorable 3 → (R (⟨k, G⟩, ε)).val = 1) ∧
        (¬ G.Colorable 3 → (R (⟨k, G⟩, ε)).val ≤ ε) := by sorry

end HDXNbhdPCP.Main
