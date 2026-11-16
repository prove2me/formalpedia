-- Prove2me | Theorems.Thm_HypercliqueCircuits_Circuits_Supplement_theorem_3
-- name    : HypercliqueCircuits.Circuits.Supplement.theorem_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T06:13:02.624338+00:00
-- url     : https://prove2.me/theorems/234379b5-f856-45a9-a77a-70967f605c08
-- title:
--   Theorem 3 — full integer k-wise matrix product
-- statement:
--   Fix $k\ge3$. There are constants $\varepsilon_k>0$, $C_k>0$ and one algorithm which computes the complete $k$-wise matrix product of any $k$ Boolean tensors of order $k$ and side length $n\ge1$ within
--
--   $$T(A_0,\ldots,A_{k-1})\le C_k n^{k+1-\varepsilon_k}.$$
--
--   The entry at $i\in[n]^k$ is the integer sum of the $n$ products obtained by replacing coordinate $j$ of tensor $A_j$ by the common contracted index. Every entry, including zeros, is output in the fixed tuple order. All constants and the program depend only on $k$. This supplies exact integer tensor multiplication, including multiplicities, for the application of Theorem 3.
--
--   Differences from the source:
--   - reading: algorithmic running time without an explicit instruction set → a finite Program Empty with actual halting execution and the published executionBits cost; reason: the supplement inherits the live mission machine; arithmetic, accessed-word lengths, and output serialization are charged, and no oracle instruction can be instantiated
--   - encoding: MP_k on k tensors with n^k Boolean entries each → Fin k-indexed Boolean tensors and n followed by all input entries; all n^k natural-valued outputs are serialized in mixed-radix order; reason: only labels and ordering are fixed; natural sum-of-products is the integer MP_k of §4.2, not a Boolean product
--   - encoding: asymptotic running time in the input size → an explicit positive multiplicative constant and a bound for every n at least 1; reason: finitely many smaller positive sizes are absorbed into the constant; n=0 is outside the power-bound convention
-- source:
--   Josh Alman, Baitian Li, Neha Pant, Kevin Pratt, Ryan Williams, Finding Hypercliques Faster Than Brute Force, STOC 2027 submission #1224 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1224.pdf, p.2, Theorem 3 (PDF 3); proof p.25 (PDF 26)

import Definitions.Def_HypercliqueCircuits_Circuits_Supplement_TensorProduct

set_option autoImplicit false

namespace HypercliqueCircuits.Circuits.Supplement

/-- Theorem 3, printed p.2 (proof p.25), PDF p.3 (proof p.26).
The output contains the full integer tensor, with serialization charged. -/
theorem theorem_3 (k : ℕ) (hk : 3 ≤ k) :
    ∃ ε C : ℝ, 0 < ε ∧ 0 < C ∧ ∃ prog : Program Empty,
      ∀ n : ℕ, 0 < n → ∀ A : BooleanTensors k n, ∃ t : ℕ,
        (execute prog (tensorInput A) t).halted = true ∧
        (execute prog (tensorInput A) t).output = tensorOutput A ∧
        (executionBits Empty.elim prog (tensorInput A) t : ℝ) ≤
          C * (n : ℝ) ^ ((k : ℝ) + 1 - ε) := by sorry

end HypercliqueCircuits.Circuits.Supplement
