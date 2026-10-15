-- Prove2me | Theorems.Thm_MIPRE_Cost_Prog_ofCode_sound
-- name    : MIPRE.Cost.Prog.ofCode_sound
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-12T16:27:00.011977+00:00
-- url     : https://prove2.me/theorems/d9955825-eda3-446a-a2dc-2c651b5be70e
-- title:
--   Soundness of the `ToPartrec` translation: $\mathrm{ofCode}(c)$ computes every value of $c$ on $\mathrm{encL}(v)$
-- statement:
--   Mathlib's `Turing.ToPartrec.Code` is a small first-order language on lists of natural numbers, with the partial semantics $c.\mathrm{eval} : \mathrm{List}\,\mathbb{N} \to \mathrm{Part}(\mathrm{List}\,\mathbb{N})$: $\mathtt{zero'}(v) = 0 :: v$; $\mathtt{succ}(v) = [\mathrm{head}(v) + 1]$, the head of the empty list being $0$; $\mathtt{tail}(v) = \mathrm{tail}(v)$; $(\mathtt{cons}\,f\,fs)(v) = \mathrm{head}(f(v)) :: fs(v)$; $(\mathtt{comp}\,f\,g)(v) = f(g(v))$; $(\mathtt{case}\,f\,g)([]) = f([])$, $(\mathtt{case}\,f\,g)(0 :: v) = f(v)$, $(\mathtt{case}\,f\,g)((n+1) :: v) = g(n :: v)$; and $(\mathtt{fix}\,f)(v)$ is the least fixed point (`PFun.fix`) that returns $\mathrm{tail}(f(v))$ if $\mathrm{head}(f(v)) = 0$ and recurses on $\mathrm{tail}(f(v))$ otherwise. Write $w \in c.\mathrm{eval}(v)$ for "$c$ on $v$ is defined, with value $w$". In the ambient cost model, lists of naturals are encoded as $\mathtt{cons}$-chains of unary numerals, $\mathrm{encL}(v)$ (`encL`; the numeral $\bar k$ is the list of $k$ copies of $\mathtt{nil}$), and $p(x) \Downarrow_t r$ (`p.Runs x r t`) denotes a run of the program $p$ on the input $x$ with result $r$ at cost $t$. The translation $\mathrm{ofCode}$ (`Prog.ofCode`) maps each construct to a program of the model — `elim`s on the input for the primitives and for $\mathtt{case}$, `let_` binders with calls of the translated subprograms for $\mathtt{cons}$ and $\mathtt{comp}$, and a `loop` for $\mathtt{fix}$.
--
--   **Statement.** For every code $c$ and lists of naturals $v, w$,
--
--   $$ w \in c.\mathrm{eval}(v) \;\Longrightarrow\; \exists t,\ \mathrm{ofCode}(c)\bigl(\mathrm{encL}(v)\bigr) \Downarrow_t \mathrm{encL}(w) . $$
--
--   This is one direction of the correctness of the translation; with `ofCode_complete` it gives that $\mathrm{ofCode}(c)$ halts on $\mathrm{encL}(v)$ exactly when $c.\mathrm{eval}(v)$ is defined (`ofCode_halts_iff`), which the compiler `exists_compile` uses to transport the halting problem of Mathlib's `Nat.Partrec.Code` into the model, for the halting form of the compression lemmas (blueprint `lem:halting-form`).
--
--   **Formalization Note**: The statement is computability-only: the cost $t$ is existential and no bound is claimed — the module docstring of the cost model explains why Mathlib's `ToPartrec.Code` cannot serve as a polynomial-time model. Lists of naturals are encoded with *unary* numerals, unlike the binary encoding of $\mathbb{N}$ used elsewhere in the development, because the translation mirrors $\mathtt{succ}$ and the head tests of $\mathtt{case}$ and $\mathtt{fix}$ by single `elim`s.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Cost/FromPartrec.lean#L139-L230; internal lemma of the formalization of blueprint lem:halting-form (the bridge from Mathlib's partial recursive functions into the model)

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

theorem MIPRE.Cost.Prog.ofCode_sound : ∀ (c : Code) (v w : List ℕ), w ∈ c.eval v →
    ∃ t, (ofCode c).Runs (encL v) (encL w) t := by sorry
