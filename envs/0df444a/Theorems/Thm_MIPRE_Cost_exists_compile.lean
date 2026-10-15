-- Prove2me | Theorems.Thm_MIPRE_Cost_exists_compile
-- name    : MIPRE.Cost.exists_compile
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-12T16:27:00.031983+00:00
-- url     : https://prove2.me/theorems/6f331a17-d5bb-4b7a-a166-f1dcf320b430
-- title:
--   The halting problem of Mathlib's partial recursive codes compiles into the ambient model, computably on descriptions
-- statement:
--   Mathlib's `Nat.Partrec.Code` is a Gödel numbering of the partial recursive functions: every code $pc$ has a partial function $pc.\mathrm{eval} : \mathbb{N} \to \mathrm{Part}\,\mathbb{N}$, and $(pc.\mathrm{eval}(0)).\mathrm{Dom}$ says that $pc$ halts on the input $0$; `Computable` is Mathlib's notion of computability between types carrying a `Primcodable` structure. In the ambient cost model, programs (`Prog`) are encoded as data by their tree serialization $\mathrm{enc}(p)$, data form a `Primcodable` type (through a Cantor-pairing bijection with $\mathbb{N}$), and $\mathrm{Halts}(p, x)$ (`Halts`) says that the program $p$ run on the input $x$ halts, with some result at some cost. The s-m-n map $s(p, d) = \mathtt{let}\ \mathtt{cons}(\mathtt{const}\ d, \mathtt{var}\ 0)\ \mathtt{in}\ p$ (`hardcode p d`) runs $p$ on the pair of the literal $d$ and its input, and $\bar n$ denotes the unary numeral of $n$ (the list of $n$ copies of $\mathtt{nil}$).
--
--   **Statement.** There is a map $\mathrm{compile} : \mathrm{Code} \to \mathrm{Prog}$ such that
--
--   1. the description map $pc \mapsto \mathrm{enc}(\mathrm{compile}(pc))$ is computable, and
--   2. for every code $pc$,
--
--   $$ \mathrm{Halts}\bigl(\mathrm{compile}(pc), \mathtt{nil}\bigr) \iff (pc.\mathrm{eval}(0)).\mathrm{Dom} . $$
--
--   This is the seam at which the development meets Mathlib's halting problem (blueprint `lem:halting-form`). The compression lemmas produce reductions $g$ from the halting problem *of the cost model*; composing with $\mathrm{compile}$ gives reductions $g \circ \mathrm{compile}$ from the halting problem of `Nat.Partrec.Code`, which is what `recursive_compression_halting`, `compressibility_criterion_halting` and ultimately the headline undecidability statement consume. Computability of the composite follows from clause 1 together with the Mathlib-computability of polynomial-time functions on computably encoded inputs (`PolyTimeFun.computable_comp`).
--
--   **Formalization Note**: The compiler carries no time bound — it is a computability-only bridge, which is why this step is available for the computable form of the main theorem but not for a polynomial-time one. Computability is stated for the *description* $\mathrm{enc}(\mathrm{compile}(pc))$ as data, since `Prog` deliberately has no `Primcodable` instance. The empty input is the datum $\mathtt{nil}$ (the encoding of the empty bit string), and the witness is $\mathrm{compile}(pc) = s(\mathrm{ofCode}(c_u), \overline{\#pc})$: the s-m-n hardcoding of the Gödel number $\#pc$ of $pc$ (`Encodable.encode pc`), as a unary numeral, into the translation of a `ToPartrec` code $c_u$ for the universal partial function $n \mapsto (\mathrm{decode}\ n).\mathrm{eval}(0)$.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Cost/FromPartrec.lean#L396-L426; internal lemma of the formalization of blueprint lem:halting-form (the bridge from Mathlib's partial recursive functions into the model)

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
open Turing.ToPartrec (Code)

theorem MIPRE.Cost.exists_compile :
    ∃ compile : Nat.Partrec.Code → Prog,
      Computable (fun pc => (encode (compile pc) : Data)) ∧
      ∀ pc : Nat.Partrec.Code, Halts (compile pc) .nil ↔ (pc.eval 0).Dom := by sorry
