-- Prove2me | Theorems.Thm_Lagrange_interpolate_eq_of_degree_lt
-- name    : Lagrange.interpolate_eq_of_degree_lt
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T09:07:15.364283+00:00
-- url     : https://prove2.me/theorems/c96c7a66-0e8d-42e1-8e72-5ef9bba51985
-- title:
--   Lagrange: interpolate eq of degree lt
-- statement:
--   The Lagrange construction uses the interpolate eq of degree lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zksecurity/simple-rbr-fri/blob/5d99bc7bcabc7b640e063f4d75f17d8262e00a8a/SimpleRbrFri/State.lean#L253-L262
-- source:
--   https://github.com/zksecurity/simple-rbr-fri/blob/5d99bc7bcabc7b640e063f4d75f17d8262e00a8a/SimpleRbrFri/State.lean#L253-L262

import Definitions.Def_SimpleRbrFri_Core
import Definitions.Def_SimpleRbrFri_State
set_option autoImplicit true
variable {F : Type*} [Field F] [DecidableEq F]

theorem Lagrange.interpolate_eq_of_degree_lt {F : Type*} [Field F] [DecidableEq F]
  (S : Finset F) (f : F → F) (Q : Polynomial F)
  (h_deg : Q.degree < S.card)
  (h_agree : ∀ x ∈ S, Q.eval x = f x) :
  Lagrange.interpolate S id f = Q := by sorry
