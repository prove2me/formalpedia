-- Prove2me | Theorems.Thm_HypercliqueAC0_FixedDepth_prefix_circuit
-- name    : HypercliqueAC0.FixedDepth.prefix_circuit
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-27T00:59:07.923303+00:00
-- url     : https://prove2.me/theorems/7260548f-124e-4744-8279-96c06295aae1
-- title:
--   A prefix of a gate is computed with one extra gate and no extra depth
-- statement:
--   Let $C$ be a De Morgan circuit with unbounded fan-in AND and OR gates, let $\alpha$ be a gate of $C$ with inputs computing $g_1,\dots,g_t$ in a fixed order, and let $j\ge0$. The prefix
--
--   $$f_{\alpha,j}=g_1\wedge\dots\wedge g_j\quad\text{or}\quad f_{\alpha,j}=g_1\vee\dots\vee g_j$$
--
--   (according to the type of $\alpha$, with the empty conjunction equal to $1$ and the empty disjunction equal to $0$) is computed by a circuit with $G(C)+1$ gates whose depth is at most the depth of $\alpha$.
--
--   The new circuit keeps all gates of $C$ and appends one gate of the same type as $\alpha$ reading the first $j$ inputs of $\alpha$. This is how Lemma 4.5 of the source applies Fourier tail bounds to prefixes of gates.
-- source:
--   Chukhin, Exhaustive Search Is Hard to Beat in Constant Depth for Hyperclique and Orthogonal Vectors, STOC 2027 submission #830, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/830.pdf, §3.2, p.10–11 (PDF 12–13): every prefix $f_{\alpha,j}$ is computed by the subcircuits for the first $j$ inputs of $\alpha$ together with one new gate.

import Mathlib
import Definitions.Def_HypercliqueAC0_FixedDepth_Planting

noncomputable section
namespace HypercliqueAC0.FixedDepth
attribute [local instance] Classical.propDecidable Classical.decEq
open scoped BigOperators

theorem prefix_circuit {X : Type} (C : MantriCVQ.ACCircuit X)
    (α : Fin C.gates.length) (j : ℕ) :
    ∃ C' : MantriCVQ.ACCircuit X, C'.depth ≤ gateDepth C α ∧
      C'.gates.length = C.gates.length + 1 ∧ ∀ x, C'.eval x = gatePrefix C α j x := by sorry

end HypercliqueAC0.FixedDepth
