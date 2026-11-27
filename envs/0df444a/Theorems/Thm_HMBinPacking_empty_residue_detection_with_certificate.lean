-- Prove2me | Theorems.Thm_HMBinPacking_empty_residue_detection_with_certificate
-- name    : HMBinPacking.empty_residue_detection_with_certificate
-- status  : Proved
-- author  : @Soh Kumabe
-- created : 2026-11-27T02:31:47.868249+00:00
-- url     : https://prove2.me/theorems/19323730-f362-49a3-9c17-b6152a06c21c
-- title:
--   Uniform quadratic-time detection and certification of empty residue polytopes
-- statement:
--   For every dimension, residue and rational query, one fixed TM2 on the registered binary input decides whether the residue polytope is empty. On empty residues it returns the required separating inequality with zero normal and right side minus one, and otherwise the one-bit nonempty indication. It is a valid strong separation answer for all queries on empty polytopes, all member queries, and the base-point query on every instance. The machine has both an explicit quadratic bound on actual input length and the exact time and output-size budgets of Lemma 7.
-- source:
--   Koana and Kumabe, High-Multiplicity Bin Packing is FPT, arXiv:2609.16923v2. Specialized machine theorem in the bit model of the paper.

import Mathlib
import Definitions.Def_HMBinPacking_OutputsWithin
import Definitions.Def_HMBinPacking_Encoding
import Theorems.Thm_HMBinPacking_lenstra_residue_optimization
import Definitions.Def_HMBinPacking_Oracles
open HMBinPacking
open ExponomialAssortment.FPTAS (encodeNat encodeRat)

theorem HMBinPacking.empty_residue_detection_with_certificate :
    ∃ M : Turing.TM2ComputableAux Bool Bool, ∀ (I : Instance) (r : Fin I.d→Fin I.d) (q : Fin I.d→ℚ),
      let input:=encodeInstance I++encodeResidue r++encVec q
      ∃ w : List Bool, OutputsWithin M input w (800*(input.length+1)^2) ∧
        OutputsWithin M input w (2^(16*I.d^3)*(inputLength I+(encVec q).length)^16) ∧
        (w=[true] ↔ (Pr I r).Nonempty) ∧
        (Pr I r=∅ → w=false::(encVec (fun _ : Fin I.d=>(0:ℚ))++encodeRat (-1))) ∧
        ((Pr I r=∅ ∨ qCast q∈Pr I r) → IsSepAnswer (Pr I r) q w) ∧
        ((∀ i,q i=((r i:ℕ):ℚ)) → IsSepAnswer (Pr I r) q w) ∧
        w.length≤(I.d+inputLength I+(encVec q).length)^16 := by sorry
