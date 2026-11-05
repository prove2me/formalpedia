-- Prove2me | Theorems.Thm_FowlerLSQC_Steane_steane_codespace
-- name    : FowlerLSQC.Steane.steane_codespace
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:37:43.287969+00:00
-- url     : https://prove2.me/theorems/57bcc75e-9b07-43ff-b31b-47a32c195e5a
-- title:
--   §10.2–10.3 — the stabilized space is span$\{|0_L\rangle,|1_L\rangle\}$; with logical $Z$ it is span$\{|0_L\rangle\}$
-- statement:
--   Let $S_0,\dots,S_5$ be the six Steane-code stabilizers (10.7)–(10.12), let $\bar Z=\mathtt{ZZZIIII}$ be logical $Z$, and let $|0_L\rangle$, $|1_L\rangle$ be the logical states (10.5)–(10.6). In the whole $2^7$-dimensional space of seven qubits,
--
--   1. the vectors stabilized by all six operators are exactly the span of the two logical states:
--
--   $$\{\psi : S_k\psi=\psi\text{ for }k=0,\dots,5\}=\operatorname{span}_{\mathbb C}\{|0_L\rangle,|1_L\rangle\};$$
--
--   2. the vectors stabilized by $\bar Z$ and all six operators are exactly the multiples of the logical zero:
--
--   $$\{\psi : \bar Z\psi=\psi\text{ and }S_k\psi=\psi\text{ for }k=0,\dots,5\}=\operatorname{span}_{\mathbb C}\{|0_L\rangle\}.$$
--
--   The first part says the stabilizer description and the codeword description define the same two-dimensional code. The second part underlies the preparation of $|0_L\rangle$ by measurement, since measuring $\bar Z$ and the six stabilizers leaves one state up to phase.
--
--   Differences from the source:
--   - reading: |0L⟩ and |1L⟩ are the only two states simultaneously stabilized by Eqs (10.7–10.12) → the joint fixed subspace equals span_ℂ{|0L⟩, |1L⟩}; reason: every superposition α|0L⟩ + β|1L⟩ is stabilized too, so "only two" means a basis of the stabilized space
--   - reading: |0L⟩ is the unique state stabilized by Z and all six stabilizers → the joint fixed subspace equals span_ℂ{|0L⟩}; reason: any scalar multiple is stabilized too, so "unique" means unique up to a scalar
--   - reading: logical Z → ZZZIIII; reason: Fig. 10.2(c) brackets the other four Z gates as optional; ZZZZZZZ is ZZZIIII times the stabilizer IIIZZZZ and gives the same subspace once the six stabilizers are imposed
--   - encoding: seven qubits with kets and Pauli strings read left to right → the register Fin 7 → Bool with wire q the character at position q from the left; reason: Lean convention of the reused register type, same instances
-- source:
--   Fowler, Towards Large-Scale Quantum Computation, arXiv:quant-ph/0506126v1, §10.2, p.113 (PDF p.131); §10.3, Fig. 10.2(c), p.117 (PDF p.135); §10.3, p.120 (PDF p.138)

import Definitions.Def_FowlerLSQC_Steane_logicalZero
import Definitions.Def_FowlerLSQC_Steane_logicalOne
import Definitions.Def_FowlerLSQC_Steane_stabilizer
import Definitions.Def_FowlerLSQC_Steane_logicalZ
import Definitions.Def_FowlerLSQC_Steane_plusOneEigenspace

namespace FowlerLSQC.Steane

/-- Fowler, *Towards Large-Scale Quantum Computation*, arXiv:quant-ph/0506126v1, §10.2, p.113
(PDF p.131), and §10.3, p.120 (PDF p.138): (i) the subspace of all seven-qubit vectors stabilized by
all six of (10.7)–(10.12) equals `span_ℂ {|0_L⟩, |1_L⟩}`; (ii) the subspace stabilized by logical `Z`
and all six equals `span_ℂ {|0_L⟩}`.

**Formalization Note.** Every superposition `α|0_L⟩ + β|1_L⟩` is stabilized too, so the book's "the
only two states" means a basis of the stabilized space and "the unique state" means unique up to a
scalar; the span equalities are the full-strength form of both claims. Logical `Z` is `ZZZIIII`
(Fig. 10.2(c)). The other representative `ZZZZZZZ` is `ZZZIIII` times `IIIZZZZ`, and gives the same
subspace once the six stabilizers are imposed. -/
theorem steane_codespace :
    (⨅ k : Fin 6, plusOneEigenspace (stabilizer k)) =
        Submodule.span ℂ {logicalZero, logicalOne} ∧
      (plusOneEigenspace logicalZ ⊓ ⨅ k : Fin 6, plusOneEigenspace (stabilizer k)) =
        Submodule.span ℂ {logicalZero} := by sorry

end FowlerLSQC.Steane
