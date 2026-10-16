-- Prove2me | Theorems.Thm_MIPRE_Cost_Data_primrec_decode_prod_nat
-- name    : MIPRE.Cost.Data.primrec_decode_prod_nat
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-15T19:38:30.235351+00:00
-- url     : https://prove2.me/theorems/ff0ced52-a4c8-4d84-a430-45bfcd94e925
-- title:
--   Decoding a pair of a bit string and a natural number out of data is primitive recursive
-- statement:
--   In the ambient cost model, data are binary trees (`Data`, with constructors $\mathtt{nil}$ and $\mathtt{cons}$) and every type the programs handle carries a size-faithful encoding (`SizedEncoding`): a map $\mathrm{encode} : \alpha \to \mathrm{Data}$ and a partial inverse $\mathrm{decode} : \mathrm{Data} \to \mathrm{Option}\ \alpha$ with $\mathrm{decode}(\mathrm{encode}\ a) = \mathrm{some}\ a$. Bit strings are encoded as $\mathtt{cons}$-chains of bits, natural numbers in binary, and a pair as the $\mathtt{cons}$ of the encodings of its components; accordingly $\mathrm{decode}_{\alpha \times \beta}(\mathtt{cons}\ a\ b)$ is $\mathrm{some}(u, v)$ when $\mathrm{decode}_\alpha(a) = \mathrm{some}\ u$ and $\mathrm{decode}_\beta(b) = \mathrm{some}\ v$, and $\mathrm{none}$ otherwise, while $\mathrm{decode}_{\alpha \times \beta}(\mathtt{nil}) = \mathrm{none}$. `Data` is a `Primcodable` type, so Mathlib's notion of a primitive recursive function (`Primrec`) applies to functions out of it.
--
--   $$ \mathrm{Primrec}\ \bigl(d \mapsto \mathrm{decode}_{\{0,1\}^* \times \mathbb N}(d)\bigr),\qquad \mathrm{Data} \to \mathrm{Option}\bigl(\{0,1\}^* \times \mathbb N\bigr). $$
--
--   This is the decoding that `exists_semidecider_prod_nat` feeds to `exists_semidecider_of_decode`: a recursively enumerable predicate on pairs $(x, n)$ of a bit string and a level is the halting set of a closed program on $\mathrm{encode}(x, n)$, which is what obligation O3 of the halting reduction requires (blueprint `lem:semidecide-encoded`).
--
--   **Formalization Note**. The statement is `MIPRE.Cost.Data.primrec_decode_prod_nat : Primrec fun d : Data => (decode d : Option (BitStr × ℕ))`, where `decode` is `SizedEncoding.decode` at the product instance and `Primrec` is Mathlib's, relative to the `Primcodable Data` instance of the formalization; `BitStr` is `List Bool`. The docstring records that the proof composes the primitive recursive decodings of the two components, `Data.primrec_decode_bitStr` and `Data.primrec_decode_nat`.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Halting/Semidecide.lean#L46-L71; blueprint lem:semidecide-encoded

import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Computability.Partrec
import Mathlib.Computability.PartrecBasis
import Mathlib.Computability.PartrecCode
import Mathlib.Computability.Primrec.List
import Mathlib.Computability.RE
import Mathlib.Computability.TuringMachine.Config
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Logic.Denumerable
import Mathlib.Logic.Function.Iterate
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_Cost_Basic
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Toolkit
import Definitions.Def_MIPRE_Foundations_Cost_Toolkit_B
import Definitions.Def_MIPRE_Foundations_Cost_Machine
import Definitions.Def_MIPRE_Foundations_Cost_Machine_B
import Definitions.Def_MIPRE_Foundations_Cost_Loops
import Definitions.Def_MIPRE_Foundations_Cost_Loops_B
import Definitions.Def_MIPRE_Foundations_Cost_Codable
import Definitions.Def_MIPRE_Foundations_Cost_Codable_B
import Definitions.Def_MIPRE_Foundations_Cost_MachineData
import Definitions.Def_MIPRE_Foundations_Cost_MachineData_B
import Definitions.Def_MIPRE_Foundations_Cost_Interpreter
import Definitions.Def_MIPRE_Foundations_Cost_Interpreter_B
import Definitions.Def_MIPRE_Foundations_Cost_Unary
import Definitions.Def_MIPRE_Foundations_Cost_MachineBound
import Definitions.Def_MIPRE_Foundations_Cost_MachineBound_B
import Definitions.Def_MIPRE_Foundations_Cost_Universal
import Definitions.Def_MIPRE_Foundations_Cost_Universal_B
import Definitions.Def_MIPRE_Foundations_Cost_Kleene
import Definitions.Def_MIPRE_Foundations_Cost_Kleene_B
import Definitions.Def_MIPRE_Foundations_Cost_FromPartrec
import Definitions.Def_MIPRE_Foundations_Cost_FromPartrec_B
import Definitions.Def_MIPRE_Foundations_Cost_Partrec
import Definitions.Def_MIPRE_Foundations_Cost_Partrec_B
import Definitions.Def_MIPRE_Foundations_Cost_Semidecide
import Definitions.Def_MIPRE_Foundations_Halting_Descriptions
import Definitions.Def_MIPRE_Foundations_Cost_Numeric
import Definitions.Def_MIPRE_Foundations_Cost_Numeric_B
import Definitions.Def_MIPRE_Foundations_Halting_Lists
import Definitions.Def_MIPRE_Foundations_Halting_Serial

open MIPRE
open MIPRE.Cost
open MIPRE.Cost.Data

theorem MIPRE.Cost.Data.primrec_decode_prod_nat :
    Primrec fun d : Data => (decode d : Option (BitStr × ℕ)) := by sorry
