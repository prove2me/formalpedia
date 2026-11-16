-- Prove2me | Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_W1F_WFw_rec
-- name    : IntMul.Kappa.R8.Bit.Oppbank.W1F_WFw_rec
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-11-15T07:52:51.250452+00:00
-- url     : https://prove2.me/theorems/5ae4928f-f705-4b3d-826c-dbf8c76a279a
-- title:
--   The stage-one word $W_1^F$ is well-formed on $(\cdot < N_L)$ (QHNetRec)
-- statement:
--   The stage-one instruction word \(W_1^F\) of the total-decoder opp-bank network \(\mathrm{QHNetRec}\) is well-formed on the local domain \(D=\{w\in\mathbb{N}:w<N_L\}\).
--
--   Fix the QHNetRec local layout, with \(N_L=31359\). Write \(W_1^F\) for the stage-one word (the concatenation of the mix, scatter, inject, copy, GREC-block, target-copy, and sweep segments). Each local instruction \(i\in W_1^F\) comprises a target code, a list of touched wires \(i_{\mathrm{touch}}\), and a list of XOR pairs \(i_{\mathrm{xor}}\). The claim is that every such instruction is well-formed on \(D\):
--   \[
--   \forall\, i\in W_1^F,\qquad
--   \bigl(\forall\, w\in i_{\mathrm{touch}},\ \ w<N_L\bigr)
--   \;\wedge\;
--   \bigl(\forall\, (p_1,p_2)\in i_{\mathrm{xor}},\ \ p_1\in i_{\mathrm{touch}}\ \wedge\ p_2\in i_{\mathrm{touch}}\bigr).
--   \]
--
--   The first conjunct is the already-proved wire bound \(\mathrm{net0O2\_W1F\_wires\_lt\_NL\_rec}\): every local wire mentioned by \(W_1^F\) (in the touch list or as an XOR endpoint) is strictly less than \(N_L\). The second conjunct is by construction of the instruction builders. Every non-sweep segment is assembled by the constructor \(\mathrm{mk}(c,el)\), which sets the XOR list equal to \(el\) and the touch list equal to the flattened endpoints of \(el\), so both endpoints of every pair automatically lie among the touched wires. Sweep instructions carry an empty XOR list, so the second conjunct holds vacuously. The argument proceeds by splitting \(W_1^F\) along its concatenations and applying this observation to each segment.
--
--   This is precisely the well-formedness hypothesis required by the already-proved lemma \(\mathrm{genF\_labGates\_rec}\) on the domain \(D=(\,\cdot\,<N_L)\). It does not assert that labels are identically \(1\), nor does it include a code-bound or \(\mathrm{nestOK}\) certificate (those belong to \(\mathrm{MovesV}\)/\(\mathrm{stage1\_seg}\)).
--
--   **Formalization Note.** This is a QHNetRec fact (`d127abea-7380-4a49-9c5c-c2103f068243`). The proof imports only the published theorem `net0O2_W1F_wires_lt_NL_rec` (`5baf9cfc`) together with `QHNetRec` and `Defs4`; it does not import the old `QHNet`, and it is not the (false) constant-label \(\mathrm{LabGates}\) claim.
-- source:
--   IntMul Kappa R8 Bit Oppbank FormalOK densify: WFw of W1F on D=(·<NL) for QHNetRec (d127abea-7380-4a49-9c5c-c2103f068243), using Proved W1F_wires_lt_NL_rec (5baf9cfc) and the mk touch-list construction. Not the constant-1 LabGates claim.

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankQHNetRec
import Mathlib
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

namespace IntMul.Kappa.R8.Bit.Oppbank
open IntMul.Kappa.R8.Bit.Oppbank.NB
open IntMul.Kappa.R8.Bit.Oppbank (NL)
/-- The stage-one word `W1F` is well-formed on the domain `(· < NL)` (QHNetRec):
every touched local wire is `< NL`, and every XOR pair lies among those wires. -/
theorem W1F_WFw_rec :
    ∀ i ∈ W1F,
      (∀ w ∈ i.2.1, w < NL) ∧ ∀ p ∈ i.2.2, p.1 ∈ i.2.1 ∧ p.2 ∈ i.2.1 := by sorry
end IntMul.Kappa.R8.Bit.Oppbank
