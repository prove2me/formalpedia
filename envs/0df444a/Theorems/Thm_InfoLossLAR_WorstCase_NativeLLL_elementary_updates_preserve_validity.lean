-- Prove2me | Theorems.Thm_InfoLossLAR_WorstCase_NativeLLL_elementary_updates_preserve_validity
-- name    : InfoLossLAR.WorstCase.NativeLLL.elementary_updates_preserve_validity
-- status  : Proved
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-20T13:14:29.576522+00:00
-- url     : https://prove2.me/theorems/ab192705-0df8-4fde-b963-4f9edce2d08f
-- title:
--   Fraction-free LLL state validity is preserved by size reduction and adjacent swaps
-- statement:
--   Consider a fraction-free integer LLL state with $n$ rows in ambient dimension $m$. Call the state valid if the stored Gram determinants and lower-triangular scaled Gram–Schmidt coefficients agree with those of its current basis. For each valid state $s$,
--
--   $$
--   \begin{aligned}
--    &\operatorname{Valid}(\operatorname{sizeReduceColumn}(s,j,k)) && (0\le j<k<n),\\
--    &\operatorname{Valid}(\operatorname{swapStep}(s,k)) && (k\in\mathbb N,\ \text{rows of }s\text{ independent}).
--   \end{aligned}
--   $$
--
--   The native swap returns the input state when $k=0$ or $k\ge n$. These two identities allow a finite LLL run to reuse its stored data after each elementary update.
-- source:
--   Kim Morrison, HexLLLTheory/ReductionInvariant.lean, theorems Hex.Internal.LLLState.sizeReduceColumn_valid and Hex.Internal.LLLState.swapStep_valid, https://github.com/leanprover/hex-lll-theory/blob/main/HexLLLTheory/ReductionInvariant.lean. These are the two preservation clauses for the native integer LLL data; the statement groups them at their shared valid input state.

import Definitions.Def_LARLLL_CurrentData

set_option autoImplicit false

namespace InfoLossLAR.WorstCase.NativeLLL

theorem elementary_updates_preserve_validity {n m : ℕ} (s : Hex.Internal.LLLState n m) (hvalid : s.Valid) :
    (∀ (j k : Fin n) (hjk : j.val < k.val), (s.sizeReduceColumn j k hjk).Valid) ∧
      (s.b.independent → ∀ k : ℕ, (s.swapStep k).Valid) := by
  sorry

end InfoLossLAR.WorstCase.NativeLLL
