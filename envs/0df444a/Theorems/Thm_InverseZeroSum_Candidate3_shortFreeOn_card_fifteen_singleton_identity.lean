-- Prove2me | Theorems.Thm_InverseZeroSum_Candidate3_shortFreeOn_card_fifteen_singleton_identity
-- name    : InverseZeroSum.Candidate3.shortFreeOn_card_fifteen_singleton_identity
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T05:30:44.262436+00:00
-- url     : https://prove2.me/theorems/e288783e-ce19-4500-bde7-994ddab2f600
-- title:
--   Candidate3: short Free On card fifteen singleton identity
-- statement:
--   A short-free set of fifteen *original positions* has a unique singleton value
--   and the singleton-plus-total-sum identity. The fibre counts and sum are
--   transported through an injective enumeration of exactly those positions.
--
--   Source: https://github.com/jfairfaxball-348/Inverse-Zero-Sum-Research/blob/c5f9e5e822020688c72b2a3bfacbf147a801e219/InverseZeroSum/Candidate3.lean#L2699-L2798
-- source:
--   https://github.com/jfairfaxball-348/Inverse-Zero-Sum-Research/blob/c5f9e5e822020688c72b2a3bfacbf147a801e219/InverseZeroSum/Candidate3.lean#L2699-L2798

module
public import Mathlib
public import Definitions.Def_InverseZeroSum_Candidate3
set_option autoImplicit true
@[expose] public section
public section
open InverseZeroSum InverseZeroSum.Candidate3
set_option maxHeartbeats 500000

theorem InverseZeroSum.Candidate3.shortFreeOn_card_fifteen_singleton_identity
    (S : PosSeq 24) {A : Finset (Fin 24)}
    (hCard : A.card = 15) (hFree : ShortFreeOn S A) :
    ∃ u : F3T,
      (A.filter (fun i => finiteModelEquiv (S i : G) = u)).card = 1 ∧
      (∀ v : F3T,
        (A.filter (fun i => finiteModelEquiv (S i : G) = v)).card ≤ 2) ∧
      (∀ v : F3T,
        (A.filter (fun i => finiteModelEquiv (S i : G) = v)).card = 1 →
          v = u) ∧
      (∑ i ∈ A, finiteModelEquiv (S i : G)) + u = 0 := by sorry
