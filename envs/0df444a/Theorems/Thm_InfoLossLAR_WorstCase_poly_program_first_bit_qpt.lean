-- Prove2me | Theorems.Thm_InfoLossLAR_WorstCase_poly_program_first_bit_qpt
-- name    : InfoLossLAR.WorstCase.poly_program_first_bit_qpt
-- status  : Proved
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-20T12:19:01.518076+00:00
-- url     : https://prove2.me/theorems/7d085bd0-d643-448a-a898-dbdd205759e2
-- title:
--   Exact first-bit simulation of a polynomial-time classical program
-- statement:
--   Let $f$ be a function on finite bit strings realized by a deterministic polynomial-time Boolean-stack program. There is a uniform quantum polynomial-time circuit family $E$ such that, for every input word $w$,
--   $$
--   \Pr[E(w)\text{ accepts}]=
--   \begin{cases}
--   1,&\text{if the first output bit of } f(w) \text{ is true},\\
--   0,&\text{otherwise}.
--   \end{cases}
--   $$
--   An empty output has acceptance probability zero. This gives an exact compiler interface for decision algorithms represented in the classical program model.
-- source:
--   Charles H. Bennett, Logical Reversibility of Computation, IBM Journal of Research and Development 17 (1973), pp. 525–532, reversible-simulation theorem, https://doi.org/10.1147/rd.176.0525. The concrete Boolean-stack input model, Clifford+T circuits, and first-bit acceptance statement are adaptations.

import Definitions.Def_InfoLossLAR_WorstCase_QPT
import Definitions.Def_QuantumMaxCutFiniteNumericRuntime

set_option autoImplicit false

open QAlgorithms.Complexity

namespace InfoLossLAR.WorstCase

theorem poly_program_first_bit_qpt (f : Str → Str) (hf : Nonempty (OAI.MetricKMedian.Binary.PolyProgram id id f)) :
    ∃ E : Family, IsQPT E ∧
      ∀ word : Str, acceptProb E word = if (f word)[0]? = some true then 1 else 0 := by
  sorry

end InfoLossLAR.WorstCase
