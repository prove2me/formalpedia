-- Prove2me | Theorems.Thm_MIPRE_Cost_Prog_ofCode_wellScoped
-- name    : MIPRE.Cost.Prog.ofCode_wellScoped
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-12T16:26:58.438971+00:00
-- url     : https://prove2.me/theorems/6031da83-cc6e-45d6-a4b5-28105d3eeeb3
-- title:
--   The translation of Mathlib's `ToPartrec` codes into the ambient model produces closed programs
-- statement:
--   Mathlib's `Turing.ToPartrec.Code` is a small first-order language on lists of natural numbers, with constructors $\mathtt{zero'}$, $\mathtt{succ}$, $\mathtt{tail}$, $\mathtt{cons}\,f\,fs$, $\mathtt{comp}\,f\,g$, $\mathtt{case}\,f\,g$ and $\mathtt{fix}\,f$, in which every partial recursive function is computable. The translation $\mathrm{ofCode} : \mathrm{Code} \to \mathrm{Prog}$ (`Prog.ofCode`) maps it construct by construct into the language of the ambient cost model: lists of naturals are encoded as $\mathtt{cons}$-chains of unary numerals $\mathrm{encL}(v)$ (`encL`; the numeral $\bar k$ is the list of $k$ copies of $\mathtt{nil}$), $\mathtt{zero'}$ prepends $\mathtt{nil}$, $\mathtt{succ}$ and $\mathtt{tail}$ are `elim`s on the input, $\mathtt{cons}$ and $\mathtt{comp}$ are `let_` binders with calls of the translated subprograms, $\mathtt{case}$ is a double `elim` on the head of the input, and $\mathtt{fix}$ is a `loop` whose body runs the translated $f$ and dispatches on the head of its result (`fixBody`). A program is *closed* (`WellScoped 1`) if it reads no variable other than its input, variable $0$, every variable of the program being bound in its binding context.
--
--   **Statement.** For every code $c$,
--
--   $$ \mathrm{ofCode}(c) \text{ is well-scoped in one variable,} $$
--
--   that is, the translation of any code is a closed program.
--
--   Closedness is the hypothesis under which calls of translated subprograms can be lifted into larger environments (`callVar_eval`, `Eval.append_of_wellScoped`) and restricted back (`callVar_runs_rev`, `Eval.of_append_of_wellScoped`); it is therefore a premise of both correctness directions `ofCode_sound` and `ofCode_complete`, and of the s-m-n transfer in the compiler `exists_compile`. It serves the halting form of the compression lemmas (blueprint `lem:halting-form`).
--
--   **Formalization Note**: `WellScoped n p` is the syntactic predicate "every variable of $p$ is below $n$ in its binding context", with `elim` adding two binders and `let_` one and `loop` requiring a nonempty environment; the translation uses the calling convention `callVar i q` $= \mathtt{let}\ \mathtt{var}\ i\ \mathtt{in}\ q$ of the closure library, which keeps callees closed.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Cost/FromPartrec.lean#L82-L95; internal lemma of the formalization of blueprint lem:halting-form (the bridge from Mathlib's partial recursive functions into the model)

import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Computability.PartrecCode
import Mathlib.Computability.Primrec.List
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
import Definitions.Def_MIPRE_Foundations_Cost_Encoding
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Loops
import Definitions.Def_MIPRE_Foundations_Cost_Unary
import Definitions.Def_MIPRE_Foundations_Cost_Toolkit
import Definitions.Def_MIPRE_Foundations_Cost_Machine
import Definitions.Def_MIPRE_Foundations_Cost_Codable
import Definitions.Def_MIPRE_Foundations_Cost_MachineData
import Definitions.Def_MIPRE_Foundations_Cost_Interpreter
import Definitions.Def_MIPRE_Foundations_Cost_MachineBound
import Definitions.Def_MIPRE_Foundations_Cost_Universal
import Definitions.Def_MIPRE_Foundations_Cost_Kleene
import Definitions.Def_MIPRE_Foundations_Cost_FromPartrec

open MIPRE
open MIPRE.Cost
open MIPRE.Cost.Prog
open Turing.ToPartrec (Code)

theorem MIPRE.Cost.Prog.ofCode_wellScoped : ∀ c : Code, (ofCode c).WellScoped 1 := by sorry
