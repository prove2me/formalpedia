-- Prove2me | Theorems.Thm_IsFoldable_pow_domain
-- name    : IsFoldable_pow_domain
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T09:03:43.038675+00:00
-- url     : https://prove2.me/theorems/91426bac-7180-4625-b2d6-d5e69bb491ee
-- title:
--   Is Foldable pow domain: Is Foldable pow domain
-- statement:
--   Key lemma: pow_domain of (m*n)-foldable set is n-foldable
--
--   Source: https://github.com/zksecurity/simple-rbr-fri/blob/5d99bc7bcabc7b640e063f4d75f17d8262e00a8a/SimpleRbrFri/Core.lean#L480-L487
-- source:
--   https://github.com/zksecurity/simple-rbr-fri/blob/5d99bc7bcabc7b640e063f4d75f17d8262e00a8a/SimpleRbrFri/Core.lean#L480-L487

import Mathlib
import Definitions.Def_SimpleRbrFri_Core
set_option autoImplicit true
open Polynomial
open scoped Pointwise
variable {F : Type*} [Field F] [DecidableEq F]

theorem IsFoldable_pow_domain {F : Type*} [Field F] [DecidableEq F] {D : Finset F} {m n : ℕ}
    (hfold : IsFoldable D (m * n)) (hm : m > 0) :
    IsFoldable (pow_domain D m) n := by sorry
