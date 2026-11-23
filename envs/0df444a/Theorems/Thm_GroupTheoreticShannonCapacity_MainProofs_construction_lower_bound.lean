-- Prove2me | Theorems.Thm_GroupTheoreticShannonCapacity_MainProofs_construction_lower_bound
-- name    : GroupTheoreticShannonCapacity.MainProofs.construction_lower_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:27:46.112826+00:00
-- url     : https://prove2.me/theorems/4a7d8013-2b27-45aa-9edf-c228a51408eb
-- title:
--   Main Proofs: construction lower bound
-- statement:
--   The Main Proofs construction uses the construction lower bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jzuiddam/GroupTheoreticShannonCapacity/blob/b3293c2c912c08768684ea560f3a59afe59920b1/GroupTheoreticShannonCapacity/MainProofs.lean#L305-L351
-- source:
--   https://github.com/jzuiddam/GroupTheoreticShannonCapacity/blob/b3293c2c912c08768684ea560f3a59afe59920b1/GroupTheoreticShannonCapacity/MainProofs.lean#L305-L351

import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Definitions.Def_GroupTheoreticShannonCapacity_Basic
import Definitions.Def_GroupTheoreticShannonCapacity_FractionGraphs
import Definitions.Def_GroupTheoreticShannonCapacity_Lattice
import Definitions.Def_GroupTheoreticShannonCapacity_Construction
import Definitions.Def_GroupTheoreticShannonCapacity_MainProofs
set_option autoImplicit true
open GroupTheoreticShannonCapacity GroupTheoreticShannonCapacity.MainProofs
open GroupTheoreticShannonCapacity Construction Lattice

theorem GroupTheoreticShannonCapacity.MainProofs.construction_lower_bound
    (n k b r s : ℕ) [NeZero n] (hk : 1 ≤ k) (hb : 1 ≤ b) (hrb : r ≤ b) :
    -- Using Construction.lean definitions
    let pVal := Construction.p n (k:ℤ) (b:ℤ) (r:ℤ) (s:ℤ)
    let qVal := Construction.q n (k:ℤ) (b:ℤ) (r:ℤ) (s:ℤ)
    -- pVal and qVal are integers (by p_q_are_integers) and positive
    -- The main result: there exists an independent AddSubgroup of size ≥ p
    -- in the n-fold strong power of the fraction graph E_{p/q}
    ∃ (p' q' : ℕ) (_ : NeZero p') (_ : 0 < q'),
      (p' : ℚ) = pVal ∧ (q' : ℚ) = qVal ∧
      ∃ S : AddSubgroup (Fin n → ZMod p'),
        (strongPower (fractionGraph p' q') n).IsIndepSet (S : Set (Fin n → ZMod p')) ∧
        Nat.card S ≥ p' := by sorry
