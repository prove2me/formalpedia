-- Prove2me | Theorems.Thm_MinDilationTree_Sublinear_theorem_1
-- name    : MinDilationTree.Sublinear.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T20:27:42.020591+00:00
-- url     : https://prove2.me/theorems/dcdb5ea6-9ed6-4c16-a743-4d44492d27b3
-- title:
--   Theorem 1 — sublinear approximation and polynomial running time
-- statement:
--   There exist a deterministic admissible program $A$, a real constant $C>0$, and an integer threshold $n_0\ge2$, all fixed together before the input, with the following property. For every $n\ge n_0$, every injective map $p:\{0,\ldots,n-1\}\to\mathbb R^2$, and every tape $\omega$, the program on $\operatorname{enc}(p)$ halts at a step $t$ and outputs a spanning tree $T$ of the points, satisfying both
--
--   $$
--   t+1\le Cn^5\log_2 n,
--   \qquad
--   \operatorname{dil}(T)\le Cn^{14/15}(\log_2 n)^3\operatorname{Opt}(p).
--   $$
--
--   The objective ranges over all spanning trees of the point set. No general-position assumption is imposed. This is the paper’s complete main theorem: the approximation guarantee and the running-time guarantee belong to one uniform algorithm.
--
--   **Formalization Note** The program is a published real-RAM program with rational literals and no random draws. Square roots, exact real arithmetic, comparisons, and indirect addressing remain available. The tape is universally quantified and is unused by admissible programs. The paper supplies no explicit time constant, and realizing its choice of $\Lambda\approx n^{1/15}$ can change the ratio constant; its $O(\cdot)$ statements therefore become the single $C,n_0$ above. Time includes the final halt instruction.
--
--   Differences from the source:
--   - reading: an algorithm with running time in O(n⁵ log n), without an explicit machine instruction set → a single admissible program of the published exact real RAM, counting every instruction including halt; reason: R0 fixes the deterministic arithmetic model used by the geometric constructions; rational literals exclude unbounded real advice and random instructions are absent
--   - encoding: an n-point set and an output spanning tree → injective Fin n coordinates encoded as [n,x₀,y₀,…] and an n×n output matrix decoded symmetrically; reason: this labels every finite distinct point set and represents every undirected tree, including collinear and cocircular inputs
--   - encoding: O(n^(14/15) log³ n) ratio and O(n⁵ log n) time → ∃ C > 0, ∃ n₀ ≥ 2, before n, p and the tape, with both bounds using log₂; reason: uniform constants and a shared sufficiently large threshold express the two asymptotic bounds; taking the larger constant and threshold preserves both
--   - encoding: real finite dilations of spanning trees and their minimum Opt → dilation and Opt in ℝ≥0∞, using infima of walk lengths and of tree dilation; reason: finite connected graphs on distinct points have finite shortest paths, and the nonempty finite family of trees attains the same minimum
-- source:
--   Sarita de Berg, Jacobus Conradi, Peter Kramer, André Nusser, Sampson Wong, STOC 2027 submission #185 (October 2026), p. 1 (PDF p. 2), Theorem 1 (Main theorem); restatement and proof p. 30 (PDF p. 31)

import Mathlib
import Definitions.Def_MinDilationTree_Sublinear_RAMEncoding

set_option autoImplicit false

namespace MinDilationTree.Sublinear

/-- Theorem 1 (Main theorem), p.1 (PDF 2), proof p.30 (PDF 31).
A single deterministic rational-literal real-RAM program, a single positive constant and a single
threshold serve all distinct planar inputs. Both the approximation ratio and running time are
required. Collinear and cocircular inputs are included. R0 fixes the machine; R4 fixes log₂.
The asymptotic threshold is at least two so that Opt and dilation concern distinct pairs. -/
theorem theorem_1 :
    ∃ A : MatMulTimeLP.Program, FewInnerTSP.Admissible A ∧
      ∃ C : ℝ, 0 < C ∧ ∃ n₀ : ℕ, 2 ≤ n₀ ∧
        ∀ n : ℕ, n₀ ≤ n → ∀ p : Fin n → Plane, Function.Injective p →
          ∀ ω : MatMulTimeLP.Tape, ∃ t : ℕ,
            MatMulTimeLP.HaltsAt A (enc p) ω t ∧
            ((t : ℝ) + 1 ≤ C * (n : ℝ) ^ 5 * log₂ n) ∧
            (outputGraph A p ω t).IsTree ∧
            dilation p (outputGraph A p ω t) ≤
              ENNReal.ofReal (C * (n : ℝ) ^ (14 / 15 : ℝ) * (log₂ n) ^ 3) * opt p := by sorry

end MinDilationTree.Sublinear
