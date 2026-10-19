-- Prove2me | Theorems.Thm_MIPRE_Cost_hardcode_wellScoped
-- name    : MIPRE.Cost.hardcode_wellScoped
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-16T15:22:34.518484+00:00
-- url     : https://prove2.me/theorems/443fcb82-eb71-4b5a-8b24-fe69ad9f9f49
-- title:
--   Lemma hardcode_wellScoped of the MIP* = RE formalization
-- statement:
--   A statement of the module `MIPRE.Foundations.Cost.Toolkit` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). The efficient computability toolkit. The efficient versions of the universal machine, the s-m-n theorem, and Kleene's recursion theorem, in the ambient cost model — blueprint Section `sec:rr-computability` (`lem:universal-tm`, `lem:smn`, `lem:kleene`), following [MNY, Lemmas 2.1–2.3]. Mathlib has the computability halves for `Nat.Partrec.Code` (`Nat.Partrec.Code.smn`, `eval_part`, `fixed_point`); everything with a time bound is new. Contents: * `hardcode`: the **efficient s-m-n**. `hardcode p d = let_ (cons (const d) (var 0)) p` binds the pair `(d, input)` as the input of `p`. The witness…
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open MIPRE.Cost
--   open Polynomial
--
--   theorem MIPRE.Cost.hardcode_wellScoped {p : Prog} (hp : p.WellScoped 1) (d : Data) :
--       (hardcode p d).WellScoped 1
--   ```
--
--   **Formalization Note** `MIPRE.Cost.hardcode_wellScoped` is declared in `MIPRE/Foundations/Cost/Toolkit.lean`, lines 62–64. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Cost/Toolkit.lean#L62-L64

import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Toolkit_B

open MIPRE
open MIPRE.Cost
open Polynomial

theorem MIPRE.Cost.hardcode_wellScoped {p : Prog} (hp : p.WellScoped 1) (d : Data) :
    (hardcode p d).WellScoped 1 := by sorry
