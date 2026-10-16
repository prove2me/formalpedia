-- Prove2me | Theorems.Thm_MIPRE_Cost_Data_size_sum_stackStep_le
-- name    : MIPRE.Cost.Data.size_sum_stackStep_le
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-15T19:33:46.562598+00:00
-- url     : https://prove2.me/theorems/7f18b635-2c80-449b-b3f1-8acf3fcde098
-- title:
--   One step of the postorder stack machine increases the total size on the stack by at most one
-- statement:
--   Data are binary trees (`nil`, `cons a b`) with $\mathrm{size}$ the number of nodes, `nil` counting one. A datum is serialized in postorder, $\mathrm{nil} \mapsto 0$ and $\mathrm{cons}(a,b) \mapsto a \cdot b \cdot 1$ (`Data.toBitsPost`), and read back by a stack machine whose step `stackStep s bit` on a stack $s$ (a list of data, top first) is: on the bit $0$, push `nil`; on the bit $1$ with at least two entries, pop $b$ then $a$ and push $\mathrm{cons}(a, b)$; on the bit $1$ with fewer than two entries, leave the stack unchanged. For every stack $s$ and bit $b$,
--
--   $$ \sum_{e \in \mathrm{stackStep}(s, b)} \mathrm{size}(e) \;\le\; \sum_{e \in s} \mathrm{size}(e) + 1. $$
--
--   A $0$ adds a node of size one; a $1$ replaces two entries of sizes $\sigma_a, \sigma_b$ by one of size $\sigma_a + \sigma_b + 1$, or does nothing. Summed over a run, the total size on the stack after reading a string is at most its length, which is how the datum a string parses to is bounded by the string's length (`size_parse_le`) and, through `natOf_lt`, how a short description names a small parameter.
--
--   **Formalization Note** The statement is `MIPRE.Cost.Data.size_sum_stackStep_le`, with `s : List Data` and `bit : Bool` explicit; the sums are `((stackStep s bit).map size).sum` and `(s.map size).sum` over ℕ. `stackStep` is total: the degenerate case of a `1` on a stack with fewer than two entries is covered, and the pop reads the top two entries with `head?.getD nil`, which the length test makes exact. The bound is on one step alone; the run `stackRun` is `List.foldl stackStep`.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Halting/Descriptions.lean#L283-L298; internal lemma of the formalization of blueprint rem:compression-abstract, item 1 (descriptions as bit strings), used in thm:halting, https://vidick.github.io/MIPRE-formalization/blueprint/

import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Computability.Primrec.List
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Logic.Denumerable
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
import Definitions.Def_MIPRE_Foundations_Halting_Descriptions

open MIPRE
open MIPRE.Cost
open MIPRE.Cost.Data

theorem MIPRE.Cost.Data.size_sum_stackStep_le (s : List Data) (bit : Bool) :
    ((stackStep s bit).map size).sum ≤ (s.map size).sum + 1 := by sorry
