-- Prove2me | Theorems.Thm_MIPRE_Repetition_nonempty_seven
-- name    : MIPRE.Repetition.nonempty_seven
-- status  : Open
-- author  : @thomasvidick
-- created : 2026-10-15T19:39:42.816648+00:00
-- url     : https://prove2.me/theorems/3a2d03dc-4d4e-4266-a43d-b6e64873e04b
-- title:
--   A parallel repetition stage exists for seven-level normal form verifiers
-- statement:
--   `MIPRE.Repetition ℓ` (blueprint `thm:parallel-repetition`, direct, not anchored, form) records the data and guarantees of parallel repetition of $\ell$-level verifiers: a constant $c > 0$ of the soundness exponent; polynomials `bound` (the output's running times and dimension) and `ansBound` (the answer length it accepts); a degree multiplier `deg`; the repeated sampler, a function of the input sampler and $(\lambda, \tau)$ with polynomial-time computable program; the polynomial-time `compute` of the repeated decider from the input programs and $(\lambda, \tau, \beta)$; and the output verifier $\mathcal{V}^{\mathrm{rep}}$. With $k(n) = 2^{\tau(|\lambda| + |n|)}$ repetitions and parse length $B(n) = 2^{\beta(|\lambda| + |n|)}$ ($|\cdot|$ the bit length): if $\mathcal{V}$ is within a budget $R$ at index $n$ then the output is within $\mathrm{bound}(\mathrm{arg})$ for running times and dimension at degree $\deg\cdot(R.k+1)$, where $\mathrm{arg}$ sums $k(n)$, $B(n)$, the components of $R$, $|\mathcal{V}|$, $\lambda, \tau, \beta, n$ and $10^{R.k}$, and accepts no answer longer than $\mathrm{ansBound}(k(n) + B(n))$ (complexity); a value-$1$ PCC strategy for $\mathcal{V}_n$ with answers at most $B(n)$ gives one for the output at $n$ (completeness); for $0 < \varepsilon \le 1$, $\mathrm{val}^*(\mathcal{V}_n) \le 1 - \varepsilon$ at answers at most $B(n)$ implies $\mathrm{val}^*(\mathcal{V}^{\mathrm{rep}}_n) \le \exp\bigl(-c\,\varepsilon^{13} k(n)/(B(n)+1)\bigr)$ (soundness). The statement: the contract holds at $\ell = 7$:
--
--   $$ \mathrm{Nonempty}\,\bigl(\mathtt{MIPRE.Repetition}\ 7\bigr). $$
--
--   It is the last of the three stage contracts `GapCompression.ofPipeline` consumes; every conditional glue theorem of this upload imports it.
--
--   **Formalization Note** In the repository the inhabitant is `MIPRE.repetition 7`, where `repetition (ℓ : ℕ) : Repetition ℓ` (`MIPRE/Background/Repetition/Verifier.lean`) packages `Repeat.repSampler` and `Repeat.repDecider` into the output `repVerifier V λ τ β`, with the vendored game-level direct repetition theorem `thm:direct-repetition-q` for soundness, whose exponent $13$ it inherits. The repetition count is the power of two just above $(\lambda n)^\tau$, written through `Nat.size` (a program writes it by walking the bits of $\lambda$ and $n$); the parse length carries the extra parameter $\beta$. The platform holds the statement only: the development proves it, in code the platform cannot host yet.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Background/Repetition/Verifier.lean

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
import Definitions.Def_MIPRE_Foundations_GameDouble
import Definitions.Def_MIPRE_Foundations_Verifier
import Definitions.Def_MIPRE_Foundations_GapCompression
import Definitions.Def_MIPRE_Foundations_VerifierValue
import Definitions.Def_MIPRE_Foundations_Pipeline_Budget
import Definitions.Def_MIPRE_Foundations_Pipeline_Repetition

theorem MIPRE.Repetition.nonempty_seven : Nonempty (MIPRE.Repetition 7) := by sorry
