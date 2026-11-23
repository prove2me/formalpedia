-- Prove2me | Theorems.Thm_GroupTheoreticShannonCapacity_Main_lattice_to_independent_set
-- name    : GroupTheoreticShannonCapacity.Main.lattice_to_independent_set
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:52:54.608854+00:00
-- url     : https://prove2.me/theorems/90dcadba-735c-4387-9b3c-948df2126fc4
-- title:
--   Main: lattice to independent set
-- statement:
--   **Lemma 2.1 (Lattice Lemma)**: Given integer matrices A, B with AB = pI and
--   minimum distance λ_∞(L(A)) ≥ q, there exists an independent set in
--   E_{p/q}^⊠n of size at least |det(B)|.
--
--   This is the core technical lemma connecting lattices to graph independence.
--
--   Source: https://github.com/jzuiddam/GroupTheoreticShannonCapacity/blob/b3293c2c912c08768684ea560f3a59afe59920b1/GroupTheoreticShannonCapacity/Main.lean#L160-L167
-- source:
--   https://github.com/jzuiddam/GroupTheoreticShannonCapacity/blob/b3293c2c912c08768684ea560f3a59afe59920b1/GroupTheoreticShannonCapacity/Main.lean#L160-L167

import Definitions.Def_GroupTheoreticShannonCapacity_MainProofs
import Mathlib.Tactic.Recall
import Definitions.Def_GroupTheoreticShannonCapacity_Main
set_option autoImplicit true
open GroupTheoreticShannonCapacity GroupTheoreticShannonCapacity.Main
open GroupTheoreticShannonCapacity MainProofs Lattice

theorem GroupTheoreticShannonCapacity.Main.lattice_to_independent_set (n : ℕ) [NeZero n]
    (A B : Matrix (Fin n) (Fin n) ℤ) (p q : ℕ) [NeZero p] (hq : 0 < q)
    (hAB : A * B = p • 1)
    (hMinDist : minDistance n (latticeOfMatrix n (A.map (↑· : ℤ → ℝ))) ≥ q) :
    ∃ S : AddSubgroup (Fin n → ZMod p),
      (strongPower (fractionGraph p q) n).IsIndepSet (S : Set (Fin n → ZMod p)) ∧
      Nat.card S ≥ Int.natAbs B.det := by sorry
