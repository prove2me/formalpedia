-- Prove2me | Theorems.Thm_LIDT_MIPStarRE_LDT_Pasting_truncatedTypeSumRecurrence
-- name    : LIDT.MIPStarRE.LDT.Pasting.truncatedTypeSumRecurrence
-- status  : Proved
-- author  : @Dengnifer
-- created : 2026-10-27T16:01:27.790364+00:00
-- url     : https://prove2.me/theorems/420141fa-b1b3-48f9-8e21-25d7581843a2
-- title:
--   Truncated Type Sum Recurrence
-- statement:
--   **Hermitian bounded recurrence for truncated type sums.** Let $G$ be a positive semidefinite operator with $G\le I$, let `d` and `prefixLen` be natural numbers, and let `tauTail` be a Boolean type pattern of any finite tail length. Write $T_{d,\ell}(\tau)$ for `truncatedTypeSums G d prefixLen tau`. Then the truncated sum is Hermitian, positive semidefinite, bounded above by the identity, and obeys the one-step recurrence obtained by prepending a Boolean bit.
--
--   $$
--   \begin{aligned}
--   T_{d,\ell}(\tau)^{\mathsf H}&=T_{d,\ell}(\tau),\\
--   0&\le T_{d,\ell}(\tau)\le I,\\
--   T_{d,\ell+1}(\tau)&=T_{d,\ell}(\operatorname{prependTypeBit}(\mathsf{true},\tau))G\\
--   &\quad+T_{d,\ell}(\operatorname{prependTypeBit}(\mathsf{false},\tau))(I-G).
--   \end{aligned}
--   $$
--
--   The sum keeps exactly those prefix type patterns whose combined Hamming weight can reach the threshold `d + 1`; each type contributes the monomial $G^{|\tau|}(I-G)^{\ell-|\tau|}$. The recurrence is the structural step used by `fromHToGAdjacentStage_paperMoveChain`, `fromHToG_SUS_context_avg_le_one`, and `fromHToG_ofGHatFactsAndHalfSandwich`.
--
--   Formalization credit: Sirui Lu, Ruixuan Deng, Yanqiao Zhu, and Zhengfeng Ji (arXiv:2609.19814). Mathematical source: Zhengfeng Ji, Anand Natarajan, Thomas Vidick, John Wright, and Henry Yuen (arXiv:2009.12982).
--
--   **Formalization Note.** The source declaration is `MIPStarRE.LDT.Pasting.truncatedTypeSumRecurrence`; its Lean statement gives the exact quantifier order and all boundary hypotheses.
-- source:
--   https://github.com/LionSR/MIPStarRE/blob/f382c801026f53a9efc260fdee707cb35e0adb15/MIPStarRE/LDT/Pasting/Bernoulli/TruncatedSums.lean#L203-L392

import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_AxisParallelLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DiagonalLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_Distribution
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_LinePolynomials
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_LowDegreePolynomial
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_OpFamily
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_OperatorExpectations
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_ParametersBase
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_ParametersFiniteAnswers
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_QuantumState
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_SubMeasurementCore
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_SubMeasurementFamilies
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_TensorPlacement
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Defs_Tuples
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Basic
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_BlockDiagonal
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_NormalizedTrace
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Order
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_TracePairing
import Mathlib

open scoped _root_.Matrix

namespace LIDT.MIPStarRE.LDT.Pasting
end LIDT.MIPStarRE.LDT.Pasting

open LIDT
/-!
# Section 12 pasting: Bernoulli truncated sums

Truncated type sums and their one-step recurrence.
-/

@[expose] public section

open LIDT.MIPStarRE.LDT.Pasting

open MIPStarRE.LDT
open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### Bernoulli recurrence weights -/

theorem LIDT.MIPStarRE.LDT.Pasting.truncatedTypeSumRecurrence
    (G : _root_.LIDT.MIPStarRE.Quantum.Op ι)
    (hGpsd : 0 ≤ G)
    (hGleOne : G ≤ 1)
    (d prefixLen : ℕ)
    {tailLen : ℕ} (τtail : _root_.LIDT.MIPStarRE.LDT.Pasting.GHatType tailLen) :
    (_root_.LIDT.MIPStarRE.LDT.Pasting.truncatedTypeSums G d prefixLen τtail)ᴴ = _root_.LIDT.MIPStarRE.LDT.Pasting.truncatedTypeSums G d prefixLen τtail ∧
      0 ≤ _root_.LIDT.MIPStarRE.LDT.Pasting.truncatedTypeSums G d prefixLen τtail ∧
      _root_.LIDT.MIPStarRE.LDT.Pasting.truncatedTypeSums G d prefixLen τtail ≤ 1 ∧
      _root_.LIDT.MIPStarRE.LDT.Pasting.truncatedTypeSums G d (prefixLen + 1) τtail =
        _root_.LIDT.MIPStarRE.LDT.Pasting.truncatedTypeSums G d prefixLen (_root_.LIDT.MIPStarRE.LDT.Pasting.prependTypeBit true τtail) * G +
          _root_.LIDT.MIPStarRE.LDT.Pasting.truncatedTypeSums G d prefixLen (_root_.LIDT.MIPStarRE.LDT.Pasting.prependTypeBit false τtail) * (1 - G) := by sorry
