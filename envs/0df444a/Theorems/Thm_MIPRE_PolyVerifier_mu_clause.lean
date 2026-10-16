-- Prove2me | Theorems.Thm_MIPRE_PolyVerifier_mu_clause
-- name    : MIPRE.PolyVerifier.mu_clause
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-15T19:25:08.478712+00:00
-- url     : https://prove2.me/theorems/fc351fb9-8582-4e4f-9560-15c12c52a17f
-- title:
--   The tabulated game's distribution is the doubled distribution of $G_z$
-- statement:
--   Let $V$ be a polynomial-time verifier and $z$ an input with `V.Efficient z` (sampler and decider halt within the polynomial budgets, and the decider rejects overlong strings). The game $G_z$ (`V.game z`) has questions and answers in `Answers (V.B z)`, the strings of length at most $B(z) = P(|z|)$; its distribution is $\mu_z(x, y) = \#\{r : |r| = B(z),\ \mathrm{questions}(z, r) = (x, y)\} / 2^{B(z)}$ and its predicate is acceptance by the decider. Its doubled game `(V.game z).doubled` is the synchronous game on $\mathrm{Bool} \times \mathrm{Answers}(B(z))$ whose distribution at $(p, q)$ is $\mu_z(p_2, q_2)$ when $p_1 = \mathrm{false}$ and $q_1 = \mathrm{true}$, and $0$ otherwise.
--
--   The table `V.tab z` is a `GameData` computed from the encoded sampler, the encoded decider and $P$: with $N$ the number of strings of length at most $B(z)$, its question alphabet is $\mathrm{Fin}(2N)$ and its answer alphabet $\mathrm{Fin}(N)$ (as `Fin (nX + 1)`, `Fin (nA + 1)` with $nX = 2N - 1$, $nA = N - 1$); its weight list puts one unit of weight, for each seed $r$ of length $B(z)$, at the index pair $(\mathrm{qIdx}(\mathrm{false}, x_r), \mathrm{qIdx}(\mathrm{true}, y_r))$, where $(x_r, y_r)$ is the budgeted sample `sampleC` on $r$ and $\mathrm{qIdx}(t, x) = \mathrm{idxOf}(x) + N\cdot[t]$. `(V.tab z).game` is the table read as a game, with distribution the normalized weight. `V.eX z : Fin (nX + 1) ≃ Bool × Answers (B z)` is the index equivalence sending $i$ to the tagged string at index $i$. Then for all $i, j$ in `Fin ((V.tab z).nX + 1)`,
--
--   $$(V.\mathrm{tab}\ z).\mathrm{game}.\mu\ i\ j \;=\; (V.\mathrm{game}\ z).\mathrm{doubled}.\mu\ (e_X\, i)\ (e_X\, j).$$
--
--   Together with `D_clause` this is the hypothesis of `quantumValue_eq_of_equiv` behind `quantumValue_tab`: the table has the quantum value of $G_z$, which is what makes a polynomial-time verifier a computable map from strings to explicit games.
--
--   **Formalization Note** `(V.tab z).game` is `GameData.game`, i.e. `g.syncGame.toGame`, whose distribution is `if g.totalWeight = 0 then (if x = 0 ∧ y = 0 then 1 else 0) else questionWeight x y / totalWeight` with natural-number weights cast to $\mathbb{R}$; the fallback point mass is part of the definition, and the statement asserts the equality of the two real numbers for every index pair. `V.eX z` is `finCongr (tab_nX z)` followed by `qEquiv (V.B z)`. The hypothesis `h : V.Efficient z` is required, `z` is implicit and `V` is a section variable.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/ClassMIPStarTab.lean#L417-L473

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
import Definitions.Def_MIPRE_Foundations_ClassMIPStar
import Definitions.Def_MIPRE_Foundations_Cost_BoundedEval
import Definitions.Def_MIPRE_Foundations_Halting_Tabulate
import Definitions.Def_MIPRE_Foundations_ClassMIPStarTab

open MIPRE
open MIPRE.PolyVerifier
open MIPRE.Cost MIPRE.Verifier
open HaltingGameValue (GameData)
variable (V : PolyVerifier)

theorem MIPRE.PolyVerifier.mu_clause {z : BitStr} (h : V.Efficient z) (i j : Fin ((V.tab z).nX + 1)) :
    (V.tab z).game.μ i j = (V.game z).doubled.μ (V.eX z i) (V.eX z j) := by sorry
