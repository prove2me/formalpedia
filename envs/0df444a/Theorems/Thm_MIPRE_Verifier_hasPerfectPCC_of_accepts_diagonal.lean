-- Prove2me | Theorems.Thm_MIPRE_Verifier_hasPerfectPCC_of_accepts_diagonal
-- name    : MIPRE.Verifier.hasPerfectPCC_of_accepts_diagonal
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-15T19:27:04.628683+00:00
-- url     : https://prove2.me/theorems/d3f889a5-41c2-4793-a787-041418409606
-- title:
--   A decider that accepts one fixed answer on every question pair has a value-one PCC strategy
-- statement:
--   Let $V$ be a normal form verifier with $\ell$ levels, $n$ an index and $T$ an answer-length bound. The question alphabet `V.Questions n` is $\mathbb{F}_2^{s(n)}$ with $s = $ `V.sampler.dim`, and `CL.toBits x` is the bit string of coordinates of a question $x$. `Answers T` is the type of bit strings of length at most $T$. `V.decider.Accepts n x y a b` means that the decider halts on the encoding of $(n, x, y, a, b)$ with output `encode true`. The game `V.game n T` has questions `V.Questions n` distributed as the sampler prescribes, answers in `Answers T`, and accepts $(a, b)$ at $(x, y)$ exactly when `Accepts n (toBits x) (toBits y) a.1 b.1`. Its doubled game `V.doubledGame n T` is the synchronous game on $\mathrm{Bool} \times$ `V.Questions n` in which Alice's questions carry the tag `false`, Bob's the tag `true`, and every other tagged pair has probability zero and is rejected. `V.HasPerfectPCC n T` says that some synchronous strategy $S$ of the doubled game is PCC — its projective measurements commute at every question pair of nonzero probability (`S.IsPCC`) — and has `S.value = 1`.
--
--   Let $a_0 \in$ `Answers T`, and assume that for all $x, y \in$ `V.Questions n`,
--   `V.decider.Accepts n (CL.toBits x) (CL.toBits y) a₀.1 a₀.1`. Then
--
--   $$V.\mathrm{HasPerfectPCC}\ n\ T .$$
--
--   This is the paper's "trivial strategy: for all questions the players return a fixed answer", and it is where the yes-instance $y_{\mathrm{yes}}$ of the classes of the compressibility criterion comes from.
--
--   **Formalization Note** No synchronicity (`IsSynchronousAt`) is asked of the decider: `HasPerfectPCC` is defined on the doubled game `(V.game n T).doubled`, whose distribution gives equal tagged questions probability zero. The hypothesis quantifies over all question pairs of `V.Questions n`, including pairs of probability zero, and `a₀.1` is the underlying bit string of the answer. `n`, `T` are implicit, `a₀` explicit, `V` a section variable, and the proposition is `MIPRE.Verifier.hasPerfectPCC_of_accepts_diagonal`.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Halting/Classes.lean#L73-L91

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Matrix.Order
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Pi
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Basic
import Definitions.Def_MIPRE_Foundations_CL_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Basic
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_CL_Sampler
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_GameTransport
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_GameDouble
import Definitions.Def_MIPRE_Foundations_Verifier
import Definitions.Def_MIPRE_Foundations_GapCompression
import Definitions.Def_MIPRE_Foundations_VerifierValue
import Definitions.Def_MIPRE_Foundations_Halting_Freeze
import Definitions.Def_MIPRE_Foundations_Halting_Classes

open MIPRE
open MIPRE.Verifier
open MIPRE.Cost
variable {ℓ : ℕ} (V : Verifier ℓ)

theorem MIPRE.Verifier.hasPerfectPCC_of_accepts_diagonal {n T : ℕ} (a₀ : Answers T)
    (hacc : ∀ x y : V.Questions n, V.decider.Accepts n (CL.toBits x) (CL.toBits y) a₀.1 a₀.1) :
    V.HasPerfectPCC n T := by sorry
