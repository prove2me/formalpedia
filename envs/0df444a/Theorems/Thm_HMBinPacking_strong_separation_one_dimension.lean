-- Prove2me | Theorems.Thm_HMBinPacking_strong_separation_one_dimension
-- name    : HMBinPacking.strong_separation_one_dimension
-- status  : Proved
-- author  : @Soh Kumabe
-- created : 2026-11-27T02:15:59.865059+00:00
-- url     : https://prove2.me/theorems/ab6251ae-8856-5576-860d-c365e3f2ce50
-- title:
--   Strong separation in dimension one with the registered time and output bounds
-- statement:
--   For every one-dimensional instance and every rational query, one fixed Turing machine returns an exact Prove2Me membership word or a strictly separating rational inequality for the residue polytope, in the step and output-size bounds of Lemma 7.
-- source:
--   Koana and Kumabe, High-Multiplicity Bin Packing is FPT, arXiv:2609.16923v2. Specialized machine theorem in the bit model of the paper.

import Mathlib
import Definitions.Def_HMBinPacking_OutputsWithin
import Definitions.Def_HMBinPacking_Encoding
import Theorems.Thm_HMBinPacking_lenstra_residue_optimization
import Definitions.Def_HMBinPacking_Oracles
open HMBinPacking
open ExponomialAssortment.FPTAS (encodeNat)

theorem HMBinPacking.strong_separation_one_dimension :
    ∃ (M : Turing.TM2ComputableAux Bool Bool) (c : ℕ),
      ∀ (I : Instance), I.d=1 → ∀ (r : Fin I.d → Fin I.d) (y : Fin I.d → ℚ), ∃ w : List Bool,
        OutputsWithin M (encodeInstance I ++ encodeResidue r ++ encVec y) w
          (2 ^ (c * I.d ^ 3) * (inputLength I + (encVec y).length) ^ c) ∧
        IsSepAnswer (Pr I r) y w ∧
        w.length ≤ (I.d + inputLength I + (encVec y).length) ^ c := by sorry
