-- Prove2me | Theorems.Thm_MIPRE_Halting_mu_clauseL
-- name    : MIPRE.Halting.mu_clauseL
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-15T19:37:57.675556+00:00
-- url     : https://prove2.me/theorems/136a66db-37e3-46c1-b714-9a63d6c4bd71
-- title:
--   The question distribution of the tabulation `tabL` is that of the doubled game of the verifier the string denotes
-- statement:
--   Fix a gap-preserving compression $G$ and an efficient universal machine $U$. A bit string $x$ denotes the verifier $\mathcal V_x$ = `Vof G U x`: the compressed sampler at the string's own parameter $\lambda_x$ = `descLam x`, with the decider datum the string carries, wrapped in the question-length check; `ansBound G x n` = $\mathrm{bound}(n + \lambda_x)$ is the answer-length cut. The tabulation `tabL G U x n` is a `GameData` (numbers $n_X, n_A$, a weight list $w$ and an acceptance list) describing the $n$-th game of $\mathcal V_x$ on the doubled question set, with the decider budgeted from $\lambda_x$. Its game `(tabL G U x n).game` has questions $\mathrm{Fin}(n_X + 1)$ and distribution $\mu(i, j) = w(i, j)/W$, where $w(i, j)$ is the total weight of the entries of $w$ at $(i, j)$ and $W$ the total weight over all index pairs (a point mass at $(0, 0)$ if $W = 0$). The doubled game `(Vof G U x).doubledGame n T` has questions $\mathrm{Bool} \times \mathbb F_2^{s(n)}$, with $\mu((\mathtt{false}, q), (\mathtt{true}, q'))$ the sampler's distribution $\mathrm{dist}_n(q, q')$ and $\mu = 0$ on every other pair of tags. The relabeling $e_X$ = `eXofL G U x n` is the equivalence $\mathrm{Fin}(n_X + 1) \simeq \mathrm{Bool} \times \mathbb F_2^{s(n)}$ under which an index, read as a binary numeral (least significant bit first), is the tag bit followed by the coordinates of the question.
--
--   For every bit string $x$, every $n \in \mathbb N$ and all $i, j \in \mathrm{Fin}(n_X + 1)$:
--
--   $$ \mu_{\mathrm{tabL}(x, n)}(i, j) \;=\; \mu_{\mathcal V_x^{\mathrm{dbl}}(n,\ \mathrm{ansBound}(x, n))}\bigl(e_X(i),\ e_X(j)\bigr). $$
--
--   No boundedness hypothesis on the string is needed: the sampler runs of the tabulation are budgeted from the compressed sampler's own time bound, which holds at every index. Distribution half of `tabL_match`; the acceptance half is `accL_mem_iff`.
--
--   **Formalization Note**. The theorem is `MIPRE.Halting.mu_clauseL`, with $G$, $U$ explicit. `tabL G U x n` is `tabOfL` applied to the encoded sampler program, the encoded (wrapped) decider program, the tabulated dimension, `ansBound G x n` twice, `G.deg`, $n$ and `descLam x`; its weight list has one entry of weight $1$ per point of $\mathbb F_2^{s}$, at the index pair of the two tagged marginals. `(tabL G U x n).game` is `HaltingGameValue.GameData.game` (`μ` by `game_μ`); `doubledGame n T` is `(V.game n T).doubled` (`μ` by `Game.doubled_μ`).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Halting/Paper/TabulateL.lean#L201-L297; internal lemma of the tabulation of the halting reduction along the paper's route (the game the search branch of the paper-route decider tests)

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
import Definitions.Def_MIPRE_Foundations_Halting_Instantiation
import Definitions.Def_MIPRE_Foundations_Halting_Paper_TabulateL

open MIPRE
open MIPRE.Halting
open MIPRE.Cost
open HaltingGameValue (GameData)
variable (G : GapCompression) (U : UniversalMachine)

theorem MIPRE.Halting.mu_clauseL (x : BitStr) (n : ℕ)
    (i j : Fin ((tabL G U x n).nX + 1)) :
    (tabL G U x n).game.μ i j
      = ((Vof G U x).doubledGame n (ansBound G x n)).μ
          (eXofL G U x n i) (eXofL G U x n j) := by sorry
