-- Prove2me | Theorems.Thm_Monodromy_IntegerPrimrec_remainder
-- name    : Monodromy.IntegerPrimrec.remainder
-- status  : Proved
-- author  : @Xiaoyang Liu
-- created : 2026-11-05T18:37:04.10225+00:00
-- url     : https://prove2.me/theorems/66aab26e-6701-4d16-bc4d-9eadeff934f2
-- title:
--   Natural Readout of Positive-Base Integer Remainders Is Primitive Recursive
-- statement:
--   For every natural B, the unary function on integers $z\mapsto\operatorname{toNat}(z\bmod(B+1))$ is primitive recursive. The modulus B+1 is positive, B=0 is allowed, and negative integer arguments are included.
--
--   Original proof dependencies: `Monodromy.IntegerPrimrec.cases`, `Monodromy.IntegerPrimrec.split`.
--
--   Proof elaboration dependencies: `Monodromy.IntegerPrimrec.cases`, `Monodromy.IntegerPrimrec.split`.
-- source:
--   Authoritative local working-tree snapshot SHA-256 e03ce2d08e07ee663140bec213fb21e995f44153a3c556c908fcf1c8d6fefe6c; repository https://github.com/ERHUTUZI123/monodromy. The remote Git base is incomplete and is not asserted to contain these declarations.
--   src/Monodromy/IntegerPrimrec.lean (file SHA-256 6dc5f3bfec05f346981b78d5c7c30dc668be696591a8e9fbc305500db06e6ae3):
--   Monodromy.IntegerPrimrec.remainder at L107-L121 [UTF-8 5050:5747].

module
public import Definitions.Def_Monodromy_IntegerPrimrec
public import Mathlib.Computability.Primrec.Basic
public import Mathlib.Data.Int.ModEq
public import Mathlib.Tactic.Ring

@[expose] public section

open Monodromy
open Monodromy.IntegerPrimrec

theorem Monodromy.IntegerPrimrec.remainder (B : ℕ) : Primrec (fun value : ℤ => (value % ((B + 1 : ℕ) : ℤ)).toNat) := by sorry
