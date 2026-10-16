-- Prove2me | Theorems.Thm_MIPRE_Cost_exists_semidecider_of_decode
-- name    : MIPRE.Cost.exists_semidecider_of_decode
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-15T19:38:24.353266+00:00
-- url     : https://prove2.me/theorems/1c4b3cdf-510e-4550-a2ce-e7e0e7bd0ef4
-- title:
--   Recursively enumerable predicates on encoded values are halting sets of closed programs of the cost model
-- statement:
--   Ambient cost model: programs `Prog`, binary-tree data `Data`, the $\mathrm{encode}$ and $\mathrm{decode}$ maps of a `SizedEncoding`; a program is closed (`WellScoped 1`) when it reads no variable but its input, and $S$ halts on $v$ (`Halts S v`) when $S$ run on the single input $v$ halts, at any cost. A predicate $p$ on a `Primcodable` type is recursively enumerable (Mathlib's `REPred p`) when it is the domain of a partial computable function.
--
--   Let $\alpha$ be a type with a `SizedEncoding`, a `Primcodable` instance and a default element (`Inhabited α`), whose decoding is primitive recursive, $\mathrm{Primrec}(d \mapsto \mathrm{decode}_\alpha(d))$, and let $p : \alpha \to \mathrm{Prop}$ be recursively enumerable. Then
--
--   $$ \exists\, S : \mathrm{Prog},\qquad S \text{ is closed} \;\wedge\; \forall a : \alpha,\ \bigl(S \text{ halts on } \mathrm{encode}(a)\bigr) \iff p(a). $$
--
--   The bit-string version `Cost.exists_semidecider` (blueprint `lem:value-lower-approx`) gives such a program on the encodings of bit strings; this lemma extends it to every type whose encoding decodes primitive recursively, in particular to pairs $(x, n)$ of a bit string and a number (`exists_semidecider_prod_nat`), whose encoding $\mathtt{cons}(\mathrm{encode}\ x, \mathrm{encode}\ n)$ is not the encoding of any bit string. Obligation O3 of the halting reduction consumes the equivalence in both directions.
--
--   **Formalization Note**. The theorem is `MIPRE.Cost.exists_semidecider_of_decode`, with implicit `{α : Type*}`, instances `[SizedEncoding α] [Primcodable α] [Inhabited α]`, hypothesis `hdec : Primrec fun d : Data => (decode d : Option α)`, implicit `{p : α → Prop}` and `hp : REPred p`; the conclusion is `∃ S : Prog, S.WellScoped 1 ∧ ∀ a : α, Halts S (encode a) ↔ p a`. `Halts S v` is `∃ r t, Eval [v] S r t`, with no bound on the cost. The instance `Inhabited α` is a hypothesis of the statement, a default element used where the predicate is read back from a bit string; `Primcodable α` is what gives `REPred p` its meaning. The docstring describes the program as `Cost.exists_semidecider`'s with the input serialized by `Prog.serProg` first.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Halting/Semidecide.lean#L75-L104; blueprint lem:semidecide-encoded

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

theorem MIPRE.Cost.exists_semidecider_of_decode {α : Type*} [SizedEncoding α] [Primcodable α] [Inhabited α]
    (hdec : Primrec fun d : Data => (decode d : Option α))
    {p : α → Prop} (hp : REPred p) :
    ∃ S : Prog, S.WellScoped 1 ∧ ∀ a : α, Halts S (encode a) ↔ p a := by sorry
