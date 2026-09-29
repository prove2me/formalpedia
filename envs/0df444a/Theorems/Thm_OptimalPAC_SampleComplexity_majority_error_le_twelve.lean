-- Prove2me | Theorems.Thm_OptimalPAC_SampleComplexity_majority_error_le_twelve
-- name    : OptimalPAC.SampleComplexity.majority_error_le_twelve
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-26T21:29:19.294921+00:00
-- url     : https://prove2.me/theorems/6edfc126-b691-4955-b3d5-63c1a6cbb96a
-- title:
--   Majority of three equal-size committees: $\mathrm{er}(h_{\mathrm{maj}})\le12\,\mathbb E[\mathcal P(\mathrm{ER}(h_I)\cap\mathrm{ER}(\tilde h))]$
-- statement:
--   Let $\mathcal P$ be a probability measure on $\mathcal X$ and $f^\star$ a measurable target. Let $G_1,G_2,G_3$ be sequences of measurable classifiers, each of the same length $n\ge1$. Put $h_i=\mathrm{Majority}(G_i)$ and $h_{\mathrm{maj}}=\mathrm{Majority}(G_1\cup G_2\cup G_3)$ (concatenation), and $\mathrm{ER}(h)=\{x: h(x)\ne f^\star(x)\}$. Let $I$ be uniform on $\{1,2,3\}$ and, given $I$, let $\tilde h$ be uniform on the $2n$ classifiers of the two sequences $G_j$, $j\ne I$ (counted with multiplicity). Then
--   $$\mathrm{er}_{\mathcal P}(h_{\mathrm{maj}};f^\star)\le12\,\mathbb E\left[\mathcal P\left(\mathrm{ER}(h_I)\cap\mathrm{ER}(\tilde h)\right)\right]=12\cdot\frac13\sum_{i=1}^3\frac1{2n}\sum_{j\ne i}\sum_{h\in G_j}\mathcal P(\mathrm{ER}(h_i)\cap\mathrm{ER}(h)),$$
--   and consequently
--   $$\mathrm{er}_{\mathcal P}(h_{\mathrm{maj}};f^\star)\le12\max_{i\in\{1,2,3\}}\ \max_{j\in\{1,2,3\}\setminus\{i\}}\ \max_{h\in G_j}\mathcal P(\mathrm{ER}(h_i)\cap\mathrm{ER}(h)).$$
--
--   In the proof of Theorem 2, $G_j=L(\mathbb A(S_0;T_j))$, which have equal lengths by the structural facts about $\mathbb A$; this step turns bounds on pairwise error intersections into a bound on the error of the majority vote.
--
--   **Formalization Note** The three sequences are indexed by $0,1,2$ in Lean. The maximum is stated as "$\le12B$ for every $B$ that bounds all $\mathcal P(\mathrm{ER}(h_i)\cap\mathrm{ER}(h))$, $h\in G_j$, $j\ne i$", which is equivalent. Ties in the majority vote go to $+1$ (`true`).
-- source:
--   Hanneke, The Optimal Sample Complexity of PAC Learning, arXiv:1507.00473v4, proof of Theorem 2, pp. 10–11 (from "Now denote h_maj" to the first two inequalities of the display on p. 11)

import Mathlib
import Definitions.Def_OptimalPAC_SampleComplexity_Model

open MeasureTheory

namespace OptimalPAC.SampleComplexity

/-- The majority-vote step of the proof of Theorem 2 (Hanneke 2016, pp. 10–11). Let `G₀, G₁, G₂`
be three sequences of measurable classifiers of the same length `n ≥ 1`, `h_i = Majority(G_i)`
and `h_maj = Majority(G₀ ∪ G₁ ∪ G₂)`. Then `er_P(h_maj; f⋆)` is at most `12` times the average
of `P(ER(h_I) ∩ ER(h̃))` over `I` uniform on the three indices and `h̃` uniform on the `2n`
classifiers of the other two sequences, and hence at most `12` times any bound on the
`P(ER(h_i) ∩ ER(h))`, `h ∈ G_j`, `j ≠ i`. -/
theorem majority_error_le_twelve {X : Type*} [MeasurableSpace X] (P : Measure X)
    [IsProbabilityMeasure P] (f : X → Bool) (hf : Measurable f)
    (G : Fin 3 → List (X → Bool)) (n : ℕ) (hn : 1 ≤ n) (hG : ∀ i, (G i).length = n)
    (hGm : ∀ i, ∀ h ∈ G i, Measurable h) :
    er P (majority (G 0 ++ G 1 ++ G 2)) f ≤
        12 * ((1 / 3 : ℝ) * ∑ i : Fin 3, (1 / (2 * (n : ℝ))) *
          ∑ j ∈ Finset.univ.erase i,
            ((G j).map (fun h => (P (ER (majority (G i)) f ∩ ER h f)).toReal)).sum) ∧
      ∀ B : ℝ, (∀ i j : Fin 3, j ≠ i → ∀ h ∈ G j,
          (P (ER (majority (G i)) f ∩ ER h f)).toReal ≤ B) →
        er P (majority (G 0 ++ G 1 ++ G 2)) f ≤ 12 * B := by sorry

end OptimalPAC.SampleComplexity
