-- Prove2me | Theorems.Thm_FowlerLSQC_Steane_stabilizer_fixes_logical_states
-- name    : FowlerLSQC.Steane.stabilizer_fixes_logical_states
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:37:43.704144+00:00
-- url     : https://prove2.me/theorems/f2f175c3-9b96-41aa-a832-bc83cc922e7c
-- title:
--   (10.7)–(10.12) — each stabilizer fixes $|0_L\rangle$ and $|1_L\rangle$
-- statement:
--   Let $S_0,\dots,S_5$ be the six Steane-code stabilizers (10.7)–(10.12), and let $|0_L\rangle$, $|1_L\rangle$ be the logical states (10.5)–(10.6). Then for every $k$,
--
--   $$S_k|0_L\rangle=|0_L\rangle\qquad\text{and}\qquad S_k|1_L\rangle=|1_L\rangle .$$
--
--   These twelve identities make the two descriptions of the code compatible. They are the elementary half of the codespace theorem of this mission.
--
--   Differences from the source:
--   - reading: operators that map the logical states |0L⟩ and |1L⟩ to themselves → each logical state is mapped to itself, S_k|0L⟩ = |0L⟩ and S_k|1L⟩ = |1L⟩; reason: the same page calls these states "stabilized", and a setwise reading would allow a swap, which none of the six performs
--   - encoding: seven qubits with kets and Pauli strings read left to right → the register Fin 7 → Bool with wire q the character at position q from the left; reason: Lean convention of the reused register type, same instances
-- source:
--   Fowler, Towards Large-Scale Quantum Computation, arXiv:quant-ph/0506126v1, §10.2, (10.5)–(10.12), p.112–113 (PDF p.130–131)

import Definitions.Def_QAlgorithms_Defs_Stabilizer
import Definitions.Def_FowlerLSQC_Steane_logicalZero
import Definitions.Def_FowlerLSQC_Steane_logicalOne
import Definitions.Def_FowlerLSQC_Steane_stabilizer

namespace FowlerLSQC.Steane

open QAlgorithms

/-- Fowler, *Towards Large-Scale Quantum Computation*, arXiv:quant-ph/0506126v1, §10.2, p.113
(PDF p.131): each of the six stabilizers (10.7)–(10.12) maps `|0_L⟩` to `|0_L⟩` and `|1_L⟩` to `|1_L⟩`
(the twelve identities behind "operators that map the logical states to themselves").

**Formalization Note.** "Map to themselves" is read pointwise, each logical state to itself, which is
the stabilizer property the page goes on to use. -/
theorem stabilizer_fixes_logical_states (k : Fin 6) :
    act (stabilizer k).toMatrix logicalZero = logicalZero ∧
      act (stabilizer k).toMatrix logicalOne = logicalOne := by sorry

end FowlerLSQC.Steane
