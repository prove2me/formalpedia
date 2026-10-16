-- Prove2me | Theorems.Thm_MIPRE_Cost_Data_canonWalk_iff
-- name    : MIPRE.Cost.Data.canonWalk_iff
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-15T19:32:07.119928+00:00
-- url     : https://prove2.me/theorems/2c5ae16f-5094-4833-acaf-28b8097bfd4a
-- title:
--   The canonicity walk accepts exactly the encodings of bit strings that are empty or end in a one
-- statement:
--   In the ambient cost model, data are binary trees (`Data`, built from `nil` and `cons`), a bit is encoded as $\mathsf{false} \mapsto \mathtt{nil}$ and $\mathsf{true} \mapsto \mathtt{cons}(\mathtt{nil}, \mathtt{nil})$, and a bit string $l \in \{0,1\}^*$ as the $\mathtt{cons}$-chain of its encoded bits ending in $\mathtt{nil}$, written $\mathrm{encode}(l)$. The function $\mathrm{canonWalk} : \mathrm{Data} \to \mathrm{Bool} \to \mathrm{Bool}$ walks a datum while recording whether the string read so far is empty or ends in a one: $\mathrm{canonWalk}(\mathtt{nil}, b) = b$; $\mathrm{canonWalk}(\mathtt{cons}(\mathtt{nil}, r), b) = \mathrm{canonWalk}(r, \mathsf{false})$; $\mathrm{canonWalk}(\mathtt{cons}(\mathtt{cons}(\mathtt{nil},\mathtt{nil}), r), b) = \mathrm{canonWalk}(r, \mathsf{true})$; and $\mathrm{canonWalk}(\mathtt{cons}(h, r), b) = \mathsf{false}$ for any other head $h$.
--
--   For every datum $d$ and Boolean $b$,
--
--   $$ \mathrm{canonWalk}(d, b) = \mathsf{true} \iff \exists\, l \in \{0,1\}^*:\quad d = \mathrm{encode}(l)\ \wedge\ \bigl(l = \varepsilon \Rightarrow b = \mathsf{true}\bigr)\ \wedge\ \bigl(l \ne \varepsilon \Rightarrow \mathrm{last}(l) = 1\bigr). $$
--
--   This is the specification of the walk performed by the program `normBinProg`, with which the wrapper decider of the halting reduction normalizes the parameter of a description (a canonical binary numeral is a bit string that is empty or ends in a one). Its instance at $b = \mathsf{true}$ is `canonWalk_eq_isCanonBin`.
--
--   **Formalization Note**. The statement is `MIPRE.Cost.Data.canonWalk_iff`. `BitStr` is `List Bool`, `encode l` is `Data.ofList Data.ofBool l`, and the last-bit condition is `l.getLast? = some true`; the empty and nonempty cases are stated as two separate implications, `(l = [] → b = true)` and `(l ≠ [] → l.getLast? = some true)`. For a datum that is not the encoding of any bit string, the right side is false because no `l` satisfies `d = encode l`. There are no hypotheses.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Halting/Lists.lean#L115-L183; internal lemma of the format-check programs of the wrapper decider (module docstring); no blueprint label is attached to this declaration

import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Computability.Primrec.List
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Logic.Denumerable
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_Cost_Basic
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Loops
import Definitions.Def_MIPRE_Foundations_Cost_Loops_B
import Definitions.Def_MIPRE_Foundations_Cost_Codable
import Definitions.Def_MIPRE_Foundations_Cost_Codable_B
import Definitions.Def_MIPRE_Foundations_Cost_Unary
import Definitions.Def_MIPRE_Foundations_Halting_Descriptions
import Definitions.Def_MIPRE_Foundations_Cost_Numeric
import Definitions.Def_MIPRE_Foundations_Cost_Numeric_B
import Definitions.Def_MIPRE_Foundations_Halting_Lists

open MIPRE
open MIPRE.Cost
open MIPRE.Cost.Data

theorem MIPRE.Cost.Data.canonWalk_iff (d : Data) (b : Bool) :
    canonWalk d b = true ↔
      ∃ l : BitStr, d = encode l ∧ (l = [] → b = true) ∧ (l ≠ [] → l.getLast? = some true) := by sorry
