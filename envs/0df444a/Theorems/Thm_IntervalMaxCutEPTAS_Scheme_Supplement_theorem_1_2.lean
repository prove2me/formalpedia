-- Prove2me | Theorems.Thm_IntervalMaxCutEPTAS_Scheme_Supplement_theorem_1_2
-- name    : IntervalMaxCutEPTAS.Scheme.Supplement.theorem_1_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T20:33:50.099273+00:00
-- url     : https://prove2.me/theorems/b358e274-8a48-4798-9fb7-dcd9ebc46da3
-- title:
--   Theorem 1.2 (companion theorem; not used in the proof of the goal) — interval sparsification
-- statement:
--   For every real interval representation of an $n$-vertex graph $G$ with $m$ edges and every real $0<\varepsilon<1$, there is an interval graph $H$ on all the same vertices, with $H\subseteq G$, and an expression of width $w$ satisfying
--
--   $$|E(G)\setminus E(H)|\le\varepsilon m,\qquad w=W(\lceil\log_2(28/\varepsilon)\rceil)\le C\varepsilon^{-2}\log_2^2(2/\varepsilon),$$
--
--   where $W(b)=3(20b2^b+1)^2+(b+1)(2^{b+1}+1)^2+1$ and $C$ is absolute. One fixed deterministic program also constructs $H$ and this expression from any integer presentation with the original endpoint comparisons and finite accuracy $\varepsilon=p/q$, $0<p<q$. Its time and space are bounded by $C(n+\lceil1/\varepsilon\rceil+1)^d$ with absolute constants. All graphs, including empty and edgeless ones, are covered. The existence clause retains arbitrary real accuracy. This is a companion structural theorem; the base EPTAS does not use its clique-width expression.
--
--   Differences from the source:
--   - encoding: a clique-width expression, without excluding the empty graph → the published positive expressions plus an empty expression evaluated only on Empty; reason: this covers n = 0; identity relabeling allowed by the published language changes no graph or width
--   - reading: word-RAM operations on words of Θ(log n) bits, including accuracy and output addresses → charged Light operations with polynomial word capacity in the numeric input parameters and addresses; reason: the construction manipulates the accuracy and its polynomial-size output; this is the same transdichotomous word convention as the immutable base mission
--   - encoding: compute the graph and a width expression → the fixed prefix packet of width, adjacency matrix, expression and explicit leaf names; reason: the executable parser and published expression evaluation fix the meaning of every output word independently of the theorem
--   - reading: accuracy ε in (0,1) as algorithm input → arbitrary real ε in the existence clause and all rational p/q in the uniform finite-input clause; reason: a machine receives a finite parameter; the real mathematical domain is retained without restriction
--   - encoding: cw(H) = O(ε⁻² log²(2/ε)) → an expression of the explicit proof width W(b) and one absolute bound constant before all inputs; reason: PDF 25 chooses b = ceil(log₂(28/ε)) and supplies this width through Lemmas 6.2–6.3; no weaker exponent or edge-loss bound is substituted
--   - encoding: real endpoints with constant-time comparisons → any integer presentation having exactly the real endpoint comparisons; reason: the base SameComparisons interface preserves every input graph, including coincident endpoints
-- source:
--   Morteza Alimi, Hani Ahmadzadeh, STOC 2027 submission #636 (October 2026), Theorem 1.2, PDF p. 3 (printed p. 2)

import Mathlib
import Definitions.Def_IntervalMaxCutEPTAS_Scheme_Supplement_WidthMachine

set_option autoImplicit false

namespace IntervalMaxCutEPTAS.Scheme.Supplement

/-- Theorem 1.2, PDF 3 (printed 2), proof PDF 25 (printed 24). Both the real-accuracy
existence clause and the uniform finite-input construction are retained, at the explicit width. -/
theorem theorem_1_2 :
    ∃ (Prog : Light.Program) (C d c : ℕ), 0 < C ∧ 1 ≤ d ∧ 1 ≤ c ∧
      (∀ (n : ℕ) (I : Rep ℝ n) (ε : ℝ), 0 < ε → ε < 1 →
        ∃ (G : SimpleGraph (Fin n)) (w : ℕ) (hG : DecidableRel G.Adj),
          @SparseInterval n I ε G hG ∧ HasExpression G w ∧
          w = explicitWidth (accuracyExponent ε) ∧
          (w : ℝ) ≤ C * ε⁻¹ ^ 2 * (Real.logb 2 (2 / ε)) ^ 2) ∧
      (∀ (n : ℕ) (I : Rep ℝ n) (J : Rep ℤ n) (p q : ℕ),
        SameComparisons I J → 0 < p → p < q →
        let ε : ℝ := (p : ℝ) / q
        ∃ T S : ℕ, T ≤ C * (n + ⌈ε⁻¹⌉₊ + 1) ^ d ∧
          S ≤ C * (n + ⌈ε⁻¹⌉₊ + 1) ^ d ∧
          Light.Ends ⟨((n + q + 2) ^ c : ℕ), S, T⟩ Prog 0 entry
            (start (encode J p q)) T (ReportsSparse I ε S)) := by sorry

end IntervalMaxCutEPTAS.Scheme.Supplement
