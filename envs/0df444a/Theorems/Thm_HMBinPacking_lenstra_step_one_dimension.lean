-- Prove2me | Theorems.Thm_HMBinPacking_lenstra_step_one_dimension
-- name    : HMBinPacking.lenstra_step_one_dimension
-- status  : Proved
-- author  : @Soh Kumabe
-- created : 2026-11-27T02:26:12.188841+00:00
-- url     : https://prove2.me/theorems/904f74f1-520d-5c87-a838-3b79aea759fe
-- title:
--   Lemma 7 Lenstra step in dimension one, for every rational objective
-- statement:
--   The full one-dimensional specialization of the registered Lenstra optimization step. One deterministic Boolean TM2 takes the official bin-packing instance, residue vector and arbitrary rational objective. It outputs an exact optimal integer vector within the original parameterized time expression. The statement also retains denominator clearing, membership in the residue polytope and attainment of both displayed maxima.
-- source:
--   Koana and Kumabe, High-Multiplicity Bin Packing is FPT, arXiv:2609.16923v2. Specialized machine theorem in the bit model of the paper.

import Mathlib
import Definitions.Def_HMBinPacking_OutputsWithin
import Definitions.Def_HMBinPacking_Encoding
import Theorems.Thm_HMBinPacking_lenstra_clear_denominators
import Theorems.Thm_HMBinPacking_lenstra_residue_optimization
open HMBinPacking
open ExponomialAssortment.FPTAS (encodeNat)

theorem HMBinPacking.lenstra_step_one_dimension :
    ∃ (M : Turing.TM2ComputableAux Bool Bool) (c : ℕ),
      ∀ (I : Instance), I.d = 1 → ∀ (r : Fin I.d → Fin I.d), ∑ i, I.s i * (r i : ℕ) ≤ I.B →
      (fun i => ((r i : ℕ) : ℤ)) ∈ Sr I r ∧
      {y' : Fin I.d → ℕ | ∑ i, I.s i * ((r i : ℕ) + I.d * y' i) ≤ I.B}.Finite ∧
      ∀ u : Fin I.d → ℚ,
      (∃ (q : ℕ) (w : Fin I.d → ℤ), 0 < q ∧ (∀ i, (q : ℚ) * u i = (w i : ℚ)) ∧
        (encodeNat I.d ++ encodeNatVec I.s ++ encodeNat I.B ++ encodeResidue r ++
          encodeIntVec w).length ≤ (I.d + inputLength I + (encVec u).length) ^ c) ∧
      ∃ y : Fin I.d → ℕ,
        OutputsWithin M (encodeInstance I ++ encodeResidue r ++ encVec u) (encodeNatVec y)
          (2 ^ (c * I.d ^ 3) * (inputLength I + (encVec u).length) ^ c) ∧
        ∑ i, I.s i * ((r i : ℕ) + I.d * y i) ≤ I.B ∧
        (fun i => (((r i : ℕ) + I.d * y i : ℕ) : ℝ)) ∈ Pr I r ∧
        IsGreatest ((fun x : Fin I.d → ℝ => ∑ i, (u i : ℝ) * x i) '' Pr I r)
          (∑ i, (u i : ℝ) * (((r i : ℕ) + I.d * y i : ℕ) : ℝ)) ∧
        IsGreatest ((fun y' : Fin I.d → ℕ => ∑ i, (u i : ℝ) * (((r i : ℕ) + I.d * y' i : ℕ) : ℝ)) ''
            {y' | ∑ i, I.s i * ((r i : ℕ) + I.d * y' i) ≤ I.B})
          (∑ i, (u i : ℝ) * (((r i : ℕ) + I.d * y i : ℕ) : ℝ)) := by sorry
