-- Prove2me | Theorems.Thm_Monodromy_IntegerPrimrec_add
-- name    : Monodromy.IntegerPrimrec.add
-- status  : Proved
-- author  : @Xiaoyang Liu
-- created : 2026-11-05T18:36:55.254537+00:00
-- url     : https://prove2.me/theorems/f1a628cb-0155-4f0e-bd20-95b000d02534
-- title:
--   Signed Integer Addition Is Primitive Recursive
-- statement:
--   The binary function $(x,y)\mapsto x+y$ on ℤ×ℤ is primitive recursive with respect to Mathlib’s canonical encodings of signed integers. There is no sign or magnitude restriction on either input.
--
--   Original proof dependencies: `Monodromy.IntegerPrimrec.cases`, `Monodromy.IntegerPrimrec.difference`, `Monodromy.IntegerPrimrec.difference_eq`, `Monodromy.IntegerPrimrec.difference_primrec`, `Monodromy.IntegerPrimrec.negSucc`, `Monodromy.IntegerPrimrec.ofNat`, `Monodromy.IntegerPrimrec.split`.
--
--   Proof elaboration dependencies: `Monodromy.IntegerPrimrec.cases`, `Monodromy.IntegerPrimrec.difference`, `Monodromy.IntegerPrimrec.difference_eq`, `Monodromy.IntegerPrimrec.difference_primrec`, `Monodromy.IntegerPrimrec.negSucc`, `Monodromy.IntegerPrimrec.ofNat`, `Monodromy.IntegerPrimrec.split`.
-- source:
--   Authoritative local working-tree snapshot SHA-256 e03ce2d08e07ee663140bec213fb21e995f44153a3c556c908fcf1c8d6fefe6c; repository https://github.com/ERHUTUZI123/monodromy. The remote Git base is incomplete and is not asserted to contain these declarations.
--   src/Monodromy/IntegerPrimrec.lean (file SHA-256 6dc5f3bfec05f346981b78d5c7c30dc668be696591a8e9fbc305500db06e6ae3):
--   Monodromy.IntegerPrimrec.add at L53-L81 [UTF-8 2073:3706].

module
public import Definitions.Def_Monodromy_IntegerPrimrec
public import Mathlib.Computability.Primrec.Basic
public import Mathlib.Data.Int.ModEq
public import Mathlib.Tactic.Ring

@[expose] public section

open Monodromy
open Monodromy.IntegerPrimrec

theorem Monodromy.IntegerPrimrec.add : Primrec₂ ((· + ·) : ℤ → ℤ → ℤ) := by sorry
