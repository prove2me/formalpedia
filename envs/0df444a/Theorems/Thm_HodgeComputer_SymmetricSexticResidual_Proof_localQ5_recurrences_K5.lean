-- Prove2me | Theorems.Thm_HodgeComputer_SymmetricSexticResidual_Proof_localQ5_recurrences_K5
-- name    : HodgeComputer.SymmetricSexticResidual.Proof.localQ5_recurrences_K5
-- status  : Proved
-- author  : @benediamond
-- created : 2026-11-24T22:21:06.48152+00:00
-- url     : https://prove2.me/theorems/ae2e511f-0196-4c7d-b989-b21846d8479a
-- title:
--   $Q_5$ and $Q_7$ linear recurrences for the integer weights `W_num_expr` in $K_5$
-- statement:
--   Proves that `W_num_expr 0..12` satisfy all 8 degree-5 $Q_5$-recurrences, 4 homogeneous $Q_7$-contractions, and the normalized top $Q_7$-contraction in $K_5$.
-- source:
--   https://github.com/hodge-computer/sextics/blob/79defa555452e16e3125da280ac2c0103a85a72d/data/symmetric-sextic-residual/LocalResidueQ5Alg.lean#L491-L749

import Definitions.Def_HodgeComputerSSR_Q5K5Master
set_option autoImplicit false
open scoped BigOperators

theorem HodgeComputer.SymmetricSexticResidual.Proof.localQ5_recurrences_K5 :
    (∀ k : Fin 8, ∑ j : Fin 6,
      SymmetricSexticResidual.LocalResidueQ5.evalSQ_K5 (SymmetricSexticResidual.Q5WeightsData.Q5_c j) *
      SymmetricSexticResidual.LocalResidueQ5.evalSQ_K5
        (SymmetricSexticResidual.LocalResidueQ5.W_num_expr ⟨k.val + j.val, by omega⟩) = 0) ∧
    (∀ m : Fin 4, ∑ j : Fin 8,
      SymmetricSexticResidual.LocalResidueQ5.evalSQ_K5 (SymmetricSexticResidual.Q5WeightsData.Q7_c j) *
      SymmetricSexticResidual.LocalResidueQ5.evalSQ_K5
        (SymmetricSexticResidual.LocalResidueQ5.W_num_expr ⟨m.val + j.val, by omega⟩) = 0) ∧
    ((SymmetricSexticResidual.Q5WeightsData.lc5_const : SymmetricSexticResidual.K5Field.K5) *
      ∑ j : Fin 8,
        SymmetricSexticResidual.LocalResidueQ5.evalSQ_K5 (SymmetricSexticResidual.Q5WeightsData.Q7_c j) *
        SymmetricSexticResidual.LocalResidueQ5.evalSQ_K5
          (SymmetricSexticResidual.LocalResidueQ5.W_num_expr ⟨4 + j.val, by omega⟩) =
      (SymmetricSexticResidual.Q5WeightsData.D_int_all : SymmetricSexticResidual.K5Field.K5) *
        SymmetricSexticResidual.LocalResidueQ5.evalSQ_K5
          SymmetricSexticResidual.Q5WeightsData.D_all_div_lc5_expr) := by sorry
