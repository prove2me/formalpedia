-- Prove2me | Theorems.Thm_NagataFactoriality_primitive_mul
-- name    : NagataFactoriality.primitive_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:46:58.171361+00:00
-- url     : https://prove2.me/theorems/68d55fe3-16ff-510f-82ad-62270b6a3435
-- title:
--   Nagata Factoriality: primitive mul
-- statement:
--   The Nagata Factoriality construction uses the primitive mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Arthur742Ramos/NagataFactoriality/blob/9ebcfa77a4f7eab6fdb663e7f151ceeb48abdff7/NagataFactoriality/Applications/Gauss.lean#L13-L15
-- source:
--   https://github.com/Arthur742Ramos/NagataFactoriality/blob/9ebcfa77a4f7eab6fdb663e7f151ceeb48abdff7/NagataFactoriality/Applications/Gauss.lean#L13-L15

import Mathlib.RingTheory.Polynomial.Content
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Definitions.Def_NagataFactoriality_Applications_Gauss
set_option autoImplicit false
open NagataFactoriality
open Polynomial

theorem NagataFactoriality.primitive_mul {R : Type*} [CommRing R] [IsDomain R] [StrongNormalizedGCDMonoid R]
    {p q : R[X]} (hp : p.IsPrimitive) (hq : q.IsPrimitive) : (p * q).IsPrimitive := by sorry
