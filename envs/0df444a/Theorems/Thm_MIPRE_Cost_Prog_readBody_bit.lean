-- Prove2me | Theorems.Thm_MIPRE_Cost_Prog_readBody_bit
-- name    : MIPRE.Cost.Prog.readBody_bit
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-15T19:27:38.07714+00:00
-- url     : https://prove2.me/theorems/1075f26d-aed0-42d5-bbba-4adf11a39173
-- title:
--   One iteration of the compressor's reading loop on a bit answer
-- statement:
--   Let `univ` be a closed program (`univ.WellScoped 1`), the universal machine the compressor's decider queries, run on inputs `cons (encode c) v`. The reading loop of the decider has the state `cons cD (cons iD acc)`: a description datum `cD`, the current bit index `iD` in binary, and the bits read so far `acc`, most recent first. Its body `readBody univ` takes the state apart, runs `univ` on `cons cD iD`, and on the answer `encode false` (`nil`) or `encode true` (`cons nil nil`) increments the index with `incProg` and pushes the bit onto the accumulator, returning the new state under the continue flag `cons nil nil`; on any other answer it stops. Let `cD`, `iD`, `acc` be data, $i$ a natural number with `iD = encode i` (the binary encoding, least significant bit first), $b$ a Boolean and $t$ a cost, and assume `univ.Runs (cons cD iD) (encode b) t`: the universal machine on `cons cD iD` halts with the bit $b$ at cost $t$. Then
--
--   $$\exists\, t' \le t + 3|c_D| + 4|i_D| + |acc| + 2\,(\mathrm{size}\ i + 2)\big(8\,\mathrm{esize}\ i + 8\,\mathrm{size}\ i + 60\big) + 30,\qquad \mathrm{Eval}\ [\mathrm{cons}\ c_D\ (\mathrm{cons}\ i_D\ acc)]\ (\mathrm{readBody}\ \mathrm{univ})\ \Big(\mathrm{cons}\ (\mathrm{cons}\ \mathrm{nil}\ \mathrm{nil})\ \big(\mathrm{cons}\ c_D\ (\mathrm{cons}\ (\mathrm{encode}\ (i + 1))\ (\mathrm{cons}\ (\mathrm{encode}\ b)\ acc))\big)\Big)\ t' ,$$
--
--   where $|\cdot|$ is `Data.size`, $\mathrm{size}\ i$ is `Nat.size i` (the binary length of $i$) and $\mathrm{esize}\ i$ is the size of `encode i`.
--
--   This is the step case of `readLoop_runs`: one bit of the described string is read and the index advanced, at a cost explicit in the sizes of the state and the cost of the query, so that the accounting of the compressor's decider can be done from these lemmas alone.
--
--   **Formalization Note** `Eval env p r t` is the timed big-step semantics; the body runs in the one-entry environment holding the state. The result `cons (cons nil nil) s'` is the loop's "continue with state `s'`" signal. `encode (i + 1)` is the binary encoding of $i + 1$ and `encode b` is `Data.ofBool b`. `cD` is an explicit section variable, `univ` an implicit one; `iD`, `acc`, `i`, `t` are implicit and `hU`, `hi`, `b`, `h` explicit. The proposition is `MIPRE.Cost.Prog.readBody_bit`.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Halting/Compressor.lean#L136-L168; paper recursive.tex, fig:halt_f (the compressor's decider is the paper's machine 𝓕 with the recursion removed)

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Computability.Halting
import Mathlib.Computability.Partrec
import Mathlib.Computability.PartrecBasis
import Mathlib.Computability.PartrecCode
import Mathlib.Computability.Primrec.List
import Mathlib.Computability.RE
import Mathlib.Computability.TuringMachine.Config
import Mathlib.Data.Complex.Basic
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.Basic
import Mathlib.Data.List.GetD
import Mathlib.Data.List.NodupEquivFin
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Logic.Denumerable
import Mathlib.Logic.Function.Iterate
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Basic
import Definitions.Def_MIPRE_Foundations_CL_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Basic
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_CL_Sampler
import Definitions.Def_MIPRE_Foundations_ValueApprox_RawInt
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_ValueApprox
import Definitions.Def_MIPRE_Foundations_ValueApprox_Cayley
import Definitions.Def_MIPRE_Foundations_ValueApprox_Projective
import Definitions.Def_MIPRE_Foundations_ValueApprox_Gaussian
import Definitions.Def_MIPRE_Foundations_ValueApprox_Norms
import Definitions.Def_MIPRE_Foundations_ValueApprox_Dense
import Definitions.Def_MIPRE_Foundations_ValueApprox_Strategy
import Definitions.Def_MIPRE_Foundations_GameTransport
import Definitions.Def_MIPRE_HaltingGameValue
import Definitions.Def_MIPRE_Foundations_GameDescription
import Definitions.Def_MIPRE_Foundations_ValueApprox_RawStrategy
import Definitions.Def_MIPRE_Foundations_ValueApprox_RawSemantics
import Definitions.Def_MIPRE_Foundations_ValueApprox_RawComplete
import Definitions.Def_MIPRE_Foundations_ValueApprox_RawPrimrec
import Definitions.Def_MIPRE_Foundations_ValueApprox_RE
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
import Definitions.Def_MIPRE_Foundations_ClassMIPStarComputable
import Definitions.Def_MIPRE_Foundations_GameDouble
import Definitions.Def_MIPRE_Foundations_Verifier
import Definitions.Def_MIPRE_Foundations_GapCompression
import Definitions.Def_MIPRE_Foundations_VerifierValue
import Definitions.Def_MIPRE_Foundations_Halting_Freeze
import Definitions.Def_MIPRE_Foundations_Halting_Classes
import Definitions.Def_MIPRE_Foundations_Halting_Descriptions
import Definitions.Def_MIPRE_Foundations_Cost_Numeric
import Definitions.Def_MIPRE_Foundations_Cost_Numeric_B
import Definitions.Def_MIPRE_Foundations_Halting_Lists
import Definitions.Def_MIPRE_Foundations_Cost_Growth
import Definitions.Def_MIPRE_Foundations_Halting_Arith
import Definitions.Def_MIPRE_Foundations_Halting_Wrapper
import Definitions.Def_MIPRE_Foundations_Halting_Enumerate
import Definitions.Def_MIPRE_Foundations_Cost_BoundedEval
import Definitions.Def_MIPRE_Foundations_Halting_Tabulate
import Definitions.Def_MIPRE_Foundations_Cost_BitQuery
import Definitions.Def_MIPRE_Foundations_Cost_Succinct
import Definitions.Def_MIPRE_Foundations_Cost_Clocked
import Definitions.Def_MIPRE_Foundations_Cost_Threshold
import Definitions.Def_MIPRE_Foundations_Compression
import Definitions.Def_MIPRE_Foundations_Halting_PolyBounded
import Definitions.Def_MIPRE_Foundations_Halting_CostBudget
import Definitions.Def_MIPRE_Foundations_Halting_Instantiation
import Definitions.Def_MIPRE_Foundations_Halting_Serial
import Definitions.Def_MIPRE_Foundations_Halting_Semidecider
import Definitions.Def_MIPRE_Foundations_Halting_WrapperCost
import Definitions.Def_MIPRE_Foundations_Halting_Strings
import Definitions.Def_MIPRE_Foundations_Halting_Reduction
import Definitions.Def_MIPRE_Foundations_Halting_Compressor

open MIPRE
open MIPRE.Cost
open MIPRE.Cost.Prog
open MIPRE.Cost.Data
variable {univ : Prog} (cD : Data)

theorem MIPRE.Cost.Prog.readBody_bit (hU : univ.WellScoped 1) {iD acc : Data} {i : ℕ} (hi : iD = encode i) (b : Bool) {t : ℕ}
    (h : univ.Runs (.cons cD iD) (encode b) t) :
    ∃ t' ≤ t + 3 * cD.size + 4 * iD.size + acc.size +
        2 * ((Nat.size i + 2) * (8 * esize i + 8 * Nat.size i + 60)) + 30,
      Eval [.cons cD (.cons iD acc)] (readBody univ)
        (.cons (.cons .nil .nil) (.cons cD (.cons (encode (i + 1)) (.cons (encode b) acc)))) t' := by sorry
