-- Prove2me | Theorems.Thm_MIPRE_Cost_Prog_normBinProg_runs
-- name    : MIPRE.Cost.Prog.normBinProg_runs
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-15T19:32:12.066445+00:00
-- url     : https://prove2.me/theorems/1181913f-309b-40d3-9296-c02a51cc3be6
-- title:
--   The normalization program computes normBin within an explicit quadratic cost bound
-- statement:
--   In the ambient cost model, `Prog.Runs p x r t` means that the program $p$, run on the one-entry environment $[x]$, halts with result $r$ at cost $t$ (`Eval [x] p r t`). The total normalization of a parameter is $\mathrm{normBin}(d) = \text{if } \mathrm{isCanonBin}(d) \text{ then } d \text{ else } \mathtt{nil}$: a datum that is a canonical binary numeral (the encoding of a bit string that is empty or ends in a one, i.e. the binary encoding of a natural number) is kept, and everything else is sent to $\mathtt{nil}$, which denotes $0$. The program $\mathrm{normBinProg} = \mathtt{let}\ (\mathtt{let}\ \mathtt{cons}(\mathtt{var}\,0, \mathtt{cons}(\mathtt{nil},\mathtt{nil}))\ \mathtt{in}\ \mathtt{loop}(\mathrm{canonBody}))\ \mathtt{in}\ \mathtt{elim}\,0\ \mathtt{nil}\ (\mathtt{var}\,3)$ builds the state $(d, \mathsf{true})$, runs the canonicity loop on it, and returns $\mathtt{nil}$ if the loop returned $\mathtt{nil}$ and the input $d$ otherwise. For a datum $d$, $\mathrm{size}(d)$ is its number of nodes and $\mathrm{spine}(d)$ its length as a list.
--
--   For every datum $d$,
--
--   $$ \exists\, t \le (\mathrm{spine}(d) + 2)\,(\mathrm{size}(d) + 25) + 3\,\mathrm{size}(d) + 10:\qquad \mathrm{normBinProg}\ \text{on the input}\ d\ \text{halts with}\ \mathrm{normBin}(d)\ \text{at cost}\ t. $$
--
--   This is the correctness and cost statement of the third of the format-check programs of the wrapper decider of the halting reduction (after the bit-walk and the equality test): the parameter of a description is normalized so that every string names a parameter. The cost is quadratic in the size of the input, as for the other walks, which copy the remainder of the list at each step.
--
--   **Formalization Note**. The statement is `MIPRE.Cost.Prog.normBinProg_runs`, with no hypotheses; the result is `normBin d` (`Data.normBin`) and the cost `t` is existential with the bound `(d.spine + 2) * (d.size + 25) + 3 * d.size + 10`, in which `Data.spine` (list length) and `Data.size` (node count) are distinct measures that the docstring both writes as $|d|$.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Halting/Lists.lean#L586-L608; the parameter normalization of the wrapper decider of blueprint rem:compression-abstract, item 1, per the module docstring; no blueprint label is attached to this declaration

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
open MIPRE.Cost.Prog
open MIPRE.Cost.Data

theorem MIPRE.Cost.Prog.normBinProg_runs (d : Data) :
    ∃ t ≤ (d.spine + 2) * (d.size + 25) + 3 * d.size + 10,
      normBinProg.Runs d (normBin d) t := by sorry
