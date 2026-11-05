-- Prove2me | Theorems.Thm_FowlerLSQC_Steane_zero_ket_stabilized
-- name    : FowlerLSQC.Steane.zero_ket_stabilized
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:37:05.418048+00:00
-- url     : https://prove2.me/theorems/2fd4f0c0-6112-4b0c-a2ab-424fd0e3be07
-- title:
--   p.120 (first clause) — $|0000000\rangle$ is a $+1$ eigenstate of logical $Z$ and (10.10)–(10.12)
-- statement:
--   The computational basis state $|0000000\rangle$ is fixed by the logical $Z$ operator $\mathtt{ZZZIIII}$ and by the three $Z$-type stabilizers $\mathtt{IIIZZZZ}$, $\mathtt{IZZIIZZ}$, $\mathtt{ZIZIZIZ}$ of (10.10)–(10.12):
--
--   $$\mathtt{ZZZIIII}\,|0000000\rangle=\mathtt{IIIZZZZ}\,|0000000\rangle=\mathtt{IZZIIZZ}\,|0000000\rangle=\mathtt{ZIZIZIZ}\,|0000000\rangle=|0000000\rangle .$$
--
--   This fact is why the source can prepare $|0_L\rangle$ from $|0000000\rangle$ by measuring only the $X$-type stabilizers.
--
--   Differences from the source:
--   - reading: State |0000000⟩ is a +1 eigenstate of logical Z and Eqs (10.10–10.12), therefore only stabilizers Eqs (10.7–10.9) need to be measured (Fig. 10.10) → the first clause, the four eigenvalue identities; reason: the clause after "therefore" is advice about the measurement circuit of Fig. 10.10, not a claim about these operators
--   - reading: logical Z → ZZZIIII; reason: Fig. 10.2(c) brackets the other four Z gates as optional, and ZZZZZZZ also fixes |0000000⟩, so the choice changes nothing
--   - encoding: seven qubits with kets and Pauli strings read left to right → the register Fin 7 → Bool with wire q the character at position q from the left; reason: Lean convention of the reused register type, same instances
-- source:
--   Fowler, Towards Large-Scale Quantum Computation, arXiv:quant-ph/0506126v1, §10.3, p.120 (PDF p.138)

import Definitions.Def_QAlgorithms_Defs_Stabilizer
import Definitions.Def_FowlerLSQC_Steane_bitString
import Definitions.Def_FowlerLSQC_Steane_stabilizer
import Definitions.Def_FowlerLSQC_Steane_logicalZ

namespace FowlerLSQC.Steane

open QAlgorithms

/-- Fowler, *Towards Large-Scale Quantum Computation*, arXiv:quant-ph/0506126v1, §10.3, p.120
(PDF p.138): `|0000000⟩` is a `+1` eigenstate of logical `Z` and of (10.10)–(10.12), i.e. of
`IIIZZZZ`, `IZZIIZZ`, `ZIZIZIZ`, which are `stabilizer 3`, `stabilizer 4`, `stabilizer 5`.

**Formalization Note.** This is the first clause of the sentence only. Its second clause, "therefore
only stabilizers Eqs (10.7–10.9) need to be measured (Fig. 10.10)", concerns a circuit and is not
stated. -/
theorem zero_ket_stabilized :
    act logicalZ.toMatrix (ket (bitString ![0, 0, 0, 0, 0, 0, 0])) =
        ket (bitString ![0, 0, 0, 0, 0, 0, 0]) ∧
      act (stabilizer 3).toMatrix (ket (bitString ![0, 0, 0, 0, 0, 0, 0])) =
        ket (bitString ![0, 0, 0, 0, 0, 0, 0]) ∧
      act (stabilizer 4).toMatrix (ket (bitString ![0, 0, 0, 0, 0, 0, 0])) =
        ket (bitString ![0, 0, 0, 0, 0, 0, 0]) ∧
      act (stabilizer 5).toMatrix (ket (bitString ![0, 0, 0, 0, 0, 0, 0])) =
        ket (bitString ![0, 0, 0, 0, 0, 0, 0]) := by sorry

end FowlerLSQC.Steane
