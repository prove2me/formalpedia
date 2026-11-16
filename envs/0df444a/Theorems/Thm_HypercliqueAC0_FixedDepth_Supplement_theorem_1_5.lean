-- Prove2me | Theorems.Thm_HypercliqueAC0_FixedDepth_Supplement_theorem_1_5
-- name    : HypercliqueAC0.FixedDepth.Supplement.theorem_1_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T20:28:58.4752+00:00
-- url     : https://prove2.me/theorems/18164405-f4e0-4487-b057-6d7e70c485cb
-- title:
--   Theorem 1.5: depth-three circuits for $2$-OV in dimension $d\ge(1+\eta)\log n$ need $c_\eta n^2$ wires
-- statement:
--   Let $2\text{-}\mathsf{OV}_{n,d}$ be Orthogonal Vectors on two lists of $n$ vectors in $\{0,1\}^d$: it outputs one exactly when some vector of the first list and some vector of the second list have no coordinate where both are one. A depth-three circuit is a De Morgan circuit (unbounded fan-in AND and OR gates over literals and constants) of depth at most three, and its wire size $W(C)$ is the number of edges of its underlying graph. $\log$ is the base-two logarithm.
--
--   For every fixed $\eta>0$ there is a constant $c_\eta>0$ such that, for all sufficiently large $n$ and every $d\ge(1+\eta)\log n$, every depth-three circuit $C$ computing $2\text{-}\mathsf{OV}_{n,d}$ satisfies
--
--   $$W(C)\ge c_\eta n^2 .$$
--
--   The input has $2nd$ bits, so a quadratic number of wires is far above the input length; this resolves the depth-three case of a conjecture of Kane and Williams for $2$-OV in logarithmic dimension.
--
--   **Formalization Note** $2\text{-}\mathsf{OV}_{n,d}$ is the published `ErrAmpOV.kOV 2 n d`. $W(C)$ is the total fan-in, the sum of the lengths of the gates' input lists, not the published `size` (gates plus wires). The constant $c_\eta$ and the threshold on $n$ depend only on $\eta$.
--
--   Differences from the source:
--   - encoding: two lists of $n$ vectors in $\{0,1\}^d$ → Boolean variables indexed by $\mathrm{Fin}\,2\times\mathrm{Fin}\,n\times\mathrm{Fin}\,d$ (the published `ErrAmpOV.kOV 2 n d`); reason: a relabeling bijection preserves every instance
--   - encoding: integers $n,d$ and the threshold for "sufficiently large $n$" → natural numbers, with real casts; reason: all are counts or lower thresholds, and a natural threshold can dominate any integer threshold
--   - encoding: the number of edges of the circuit graph, under the §3.2 convention that every gate reaches the output → the total length of the gates' input lists over arbitrary circuits, including unused gates and repeated entries; reason: pruning unused gates and deleting repeated entries preserve output and depth and cannot increase this count, and on a pruned circuit without repetitions it equals the number of edges
-- source:
--   Nikolai Chukhin, Exhaustive Search Is Hard to Beat in Constant Depth for Hyperclique and Orthogonal Vectors, STOC 2027 submission #830 (October 2026), source.pdf SHA-256 bd73fd887fe562527226e0ea2da24a55552a73cf89c2e90406a28965424a12de, p.24 (PDF p.26), Theorem 1.5 (also stated p.5, PDF p.7); wire size §3.2 p.10 (PDF p.12)

import Mathlib
import Definitions.Def_ErrAmpOV_kOV
import Definitions.Def_HypercliqueAC0_FixedDepth_Supplement_Wires

noncomputable section

namespace HypercliqueAC0.FixedDepth.Supplement

/-- Theorem 1.5, p. 24 (PDF 26), stated also on p. 5 (PDF 7). `2-OV_{n,d}` is
`ErrAmpOV.kOV 2 n d`; a depth-three circuit has depth at most three; `log` is base two; the wire
size `W(C)` is the total fan-in `wires C`. The constant `c_η` and the threshold `n₀` depend only
on `η`, and every dimension `d ≥ (1+η) log n` is covered. -/
theorem theorem_1_5 (η : ℝ) (hη : 0 < η) :
    ∃ c : ℝ, 0 < c ∧ ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ∀ d : ℕ,
      (1 + η) * Real.logb 2 n ≤ (d : ℝ) →
      ∀ C : MantriCVQ.ACCircuit (Fin 2 × Fin n × Fin d), C.depth ≤ 3 →
        (∀ x, C.eval x = ErrAmpOV.kOV 2 n d x) →
        c * (n : ℝ) ^ 2 ≤ (wires C : ℝ) := by sorry

end HypercliqueAC0.FixedDepth.Supplement
