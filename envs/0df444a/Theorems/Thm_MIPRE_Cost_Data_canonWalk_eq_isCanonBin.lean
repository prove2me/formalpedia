-- Prove2me | Theorems.Thm_MIPRE_Cost_Data_canonWalk_eq_isCanonBin
-- name    : MIPRE.Cost.Data.canonWalk_eq_isCanonBin
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-15T19:32:21.83469+00:00
-- url     : https://prove2.me/theorems/1706cdac-ffc8-495d-9b67-8d5b6ab62e69
-- title:
--   The canonicity walk started on true computes the canonical-binary-numeral test
-- statement:
--   In the ambient cost model, natural numbers are encoded in binary, least significant bit first (Mathlib's `Nat.bits`), as bit strings, and bit strings as $\mathtt{cons}$-chains of encoded bits; so the encoding of a natural number is a bit string that is empty (the number $0$) or ends in a one. The test $\mathrm{isCanonBin} : \mathrm{Data} \to \mathrm{Bool}$ decodes a datum $d$ as a bit string: if it decodes to $l$, the result is the Boolean of $l = \varepsilon \vee \mathrm{last}(l) = 1$; if it does not decode, the result is $\mathsf{false}$. The walk $\mathrm{canonWalk}(d, b)$ (specified by `canonWalk_iff`) reads $d$ as a list of bits, failing on any non-bit element, and returns whether the string read is empty (in which case it returns the start value $b$) or ends in a one.
--
--   For every datum $d$,
--
--   $$ \mathrm{canonWalk}(d, \mathsf{true}) = \mathrm{isCanonBin}(d). $$
--
--   This identifies what the loop of the program `normBinProg` computes with the normalization test behind $\mathrm{normBin}(d) = \text{if } \mathrm{isCanonBin}(d) \text{ then } d \text{ else } \mathtt{nil}$, the total normalization of a parameter in which canonical binary numerals are kept and everything else reads as zero; `normBinProg_runs` uses it to state the program's output as $\mathrm{normBin}(d)$.
--
--   **Formalization Note**. The statement is `MIPRE.Cost.Data.canonWalk_eq_isCanonBin`, an equality of Booleans with no hypotheses. `isCanonBin` is a `match` on `decode d : Option BitStr`, with `decide (l = [] ∨ l.getLast? = some true)` in the `some l` branch and `false` in the `none` branch; `normBin` and `natOf d = ((decode (normBin d) : Option ℕ)).getD 0`, the parameter a datum denotes, are defined in `MIPRE/Foundations/Halting/Descriptions.lean`.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Halting/Lists.lean#L185-L209; internal lemma of the format-check programs of the wrapper decider (module docstring); no blueprint label is attached to this declaration

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

theorem MIPRE.Cost.Data.canonWalk_eq_isCanonBin (d : Data) : canonWalk d true = isCanonBin d := by sorry
