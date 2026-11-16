-- Prove2me | Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_genF_labGates_rec
-- name    : IntMul.Kappa.R8.Bit.Oppbank.genF_labGates_rec
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-11-15T07:43:06.021343+00:00
-- url     : https://prove2.me/theorems/b41dc741-9fee-4f84-876e-b0b01ab54207
-- title:
--   Generated chunks are label-consistent (QHNetRec $\mathrm{genF}$)
-- statement:
--   On the total-decoder network `QHNetRec`, chunks produced by the label generator \(\mathrm{genF}\) are label-consistent.
--
--   Fix a field size \(N\), a wire embedding \(\iota\colon\mathbb{N}\to\mathrm{Wr}\) that is injective on a domain \(D\subseteq\mathbb{N}\), a family of frame matrices \(\mathrm{lab}(c)\) indexed by codes, and an edge family \(E\). Let \(W\) be a list of local instructions that is well-formed on \(D\) (every touched wire lies in \(D\), and every XOR pair is among those wires), and let \(f\) be an initial code assignment. Write \(\mathrm{cs}=(\mathrm{genF}\,f\,W)_2\) for the generated chunk list and \(\mathrm{chunkProg}(\iota,E,\mathrm{cs})\) for the corresponding global program (one frame-change edge per move, then one XOR gate per local pair).
--
--   Assume that every generated move from an old code \(o\) to a new code \(c\) carries frames along:
--   $$
--   \mathrm{edgeMat}_N\bigl(E(o,c)\bigr)\cdot\mathrm{lab}(o)=\mathrm{lab}(c).
--   $$
--   If a labelling \(L\) agrees with the initial frames on the embedded domain — \(L(\iota(w))=\mathrm{lab}(f(w))\) whenever \(D(w)\) — then:
--
--   - the generated program is label-consistent starting from \(L\), in the sense of \(\mathrm{LabGates}_N\);
--   - after the program, the label at \(\iota(w)\) is the frame of the final code \((\mathrm{genF}\,f\,W)_1(w)\);
--   - labels of wires outside the image \(\iota(D)\) are left unchanged.
--
--   The argument is by induction on \(W\). For a single instruction the moves are applied first; injectivity of \(\iota\) on \(D\) ensures that a move of one wire does not disturb another, and the edge-matrix hypothesis updates the moved wire's label from \(\mathrm{lab}(o)\) to \(\mathrm{lab}(c)\). After the moves, every touched wire sits at the instruction's target code, so the subsequent XOR gates see equal labels on their support and act as the identity on the labelling. The inductive step concatenates this block with the program of the tail, using the decomposition of \(\mathrm{LabGates}\) under list append.
--
--   **Formalization Note.** This is the QHNetRec retarget of the published R6 theorem `IntMul.Kappa.R6.Bit.genF_labGates` (`9a6c078b-c567-48f9-8d40-e650f78ed5c4`). The platform theorem applies to the R6 `genF` / `chunkProg` constants and cannot be used on the inlined QHNetRec copies, so the proof is ported rather than imported. The statement is specialized to the QHNetRec carrier \(\mathrm{Wr}=\mathrm{Fin}\,W\oplus\mathrm{Fin}\,T_{\mathrm{mp}}\) and to coefficient ring \(\mathbb{Z}/2\mathbb{Z}\), field size \(529\), matching `NB.chunkProg` and `NB.xorG`. It imports only `QHNetRec` (and `Defs4` / Mathlib), not the old `QHNet`, and does not close `9a6c078b`.
-- source:
--   IntMul Kappa R8 Bit Oppbank FormalOK densify: QHNetRec retarget of R6 genF_labGates (9a6c078b-c567-48f9-8d40-e650f78ed5c4) onto the inlined total-decoder genF/chunkProg of QHNetRec (d127abea-7380-4a49-9c5c-c2103f068243). Does not close or replace 9a6c078b.

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankQHNetRec
import Mathlib
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

namespace IntMul.Kappa.R8.Bit.Oppbank
open IntMul.Kappa.R6.Bit (LabGates labStepH FMat edgeMat Edge)
open IntMul.Kappa.R8.Bit.Oppbank.NB
theorem genF_labGates_rec {N : ℕ} (ι : ℕ → Wr) (D : ℕ → Prop) (lab : ℕ → FMat 529 N)
    (E : ℕ → ℕ → Edge 529) (hι : ∀ w w', D w → D w' → ι w = ι w' → w = w') :
    ∀ (W : List LInstr) (f : ℕ → ℕ) (L : Wr → FMat 529 N),
      (∀ i ∈ W, (∀ w ∈ i.2.1, D w) ∧ ∀ p ∈ i.2.2, p.1 ∈ i.2.1 ∧ p.2 ∈ i.2.1) →
      (∀ ch ∈ (genF f W).2, ∀ mv ∈ ch.2.1, edgeMat N (E mv.2 ch.1) * lab mv.2 = lab ch.1) →
      (∀ w, D w → L (ι w) = lab (f w)) →
      LabGates N (chunkProg ι E (genF f W).2) L ∧
        (∀ w, D w → (chunkProg ι E (genF f W).2).foldl (labStepH N) L (ι w) =
          lab ((genF f W).1 w)) ∧
        ∀ x, (∀ w, D w → ι w ≠ x) → (chunkProg ι E (genF f W).2).foldl (labStepH N) L x = L x := by sorry
end IntMul.Kappa.R8.Bit.Oppbank
