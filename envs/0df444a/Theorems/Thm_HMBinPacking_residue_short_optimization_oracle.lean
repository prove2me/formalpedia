-- Prove2me | Theorems.Thm_HMBinPacking_residue_short_optimization_oracle
-- name    : HMBinPacking.residue_short_optimization_oracle
-- status  : Proved
-- author  : @Soh Kumabe
-- created : 2026-11-26T10:12:19.809382+00:00
-- url     : https://prove2.me/theorems/9a32c6fd-3c2c-44c0-93d3-38d43aae296c
-- title:
--   Lemma 7, a common bit bound for vertices and strong optimization answers
-- statement:
--   For a bin packing instance with $d$ item types, capacity $B$, and a residue $r$ that itself fits, every extreme point of $P_r$ has a rational encoding of at most $d(2\,\mathrm{size}(B)+5)$ bits. There is a single binary-word oracle that returns an exact maximizer of every rational linear objective on $P_r$ with the same output-length bound. Here $\mathrm{size}(B)$ is the binary digit length. This asserts existence and encoding length of correct answers. No running time for the oracle is asserted.
-- source:
--   Koana, Kumabe, High-Multiplicity Bin Packing is FPT, arXiv:2609.16923v2, Proof of Lemma 7, p.5. Geometric or encoding subclaim from the proof of Lemma 7.

import Definitions.Def_HMBinPacking_Oracles
import Definitions.Def_HMBinPacking_ILP
import Theorems.Thm_HMBinPacking_lenstra_residue_optimization
import Mathlib.Analysis.Convex.Extreme
import Mathlib.Data.Nat.Size
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
open HMBinPacking Finset ExponomialAssortment.FPTAS

namespace HMBinPacking

theorem residue_short_optimization_oracle (I : Instance) (r : Fin I.d → Fin I.d) (hr : ∑ i, I.s i * (r i : ℕ) ≤ I.B) :
    (∀ x ∈ Set.extremePoints ℝ (Pr I r), ∃ v : Fin I.d → ℚ, qCast v = x ∧
      (encVec v).length ≤ I.d * (2 * I.B.size + 5)) ∧
    ∃ O : List Bool → List Bool, ∀ u : Fin I.d → ℚ,
      IsOptAnswer (Pr I r) u (O (encVec u)) ∧
      (O (encVec u)).length ≤ I.d * (2 * I.B.size + 5) := by sorry

end HMBinPacking
