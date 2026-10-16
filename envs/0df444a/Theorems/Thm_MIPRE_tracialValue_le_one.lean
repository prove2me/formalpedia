-- Prove2me | Theorems.Thm_MIPRE_tracialValue_le_one
-- name    : MIPRE.tracialValue_le_one
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-15T19:25:22.507751+00:00
-- url     : https://prove2.me/theorems/0bb209a7-1750-4095-b40c-0a16d06ec44f
-- title:
--   The tracial value of a projective measurement family in a synchronous game is at most one
-- statement:
--   Let $X$ and $A$ be finite types with decidable equality on $A$, and let $\mathcal{A}$ be a ring with a star structure and a $\mathbb{C}$-module structure (`Ring 𝒜`, `StarRing 𝒜`, `Module ℂ 𝒜`; no norm is assumed). Let $G$ be a synchronous game on $(X, A)$: a probability distribution $\mu$ on $X \times X$ and a decision predicate $D : X \to X \to A \to A \to \mathrm{Bool}$ rejecting unequal answers to equal questions. A tracial state $\tau$ on $\mathcal{A}$ is a $\mathbb{C}$-linear functional with $0 \le \tau(m^* m)$ for all $m$ (in the partial order of $\mathbb{C}$), $\tau(1) = 1$ and $\tau(mn) = \tau(nm)$. A projective measurement family $P$ on $(X, A)$ in $\mathcal{A}$ is a family of operators $M^x_a \in \mathcal{A}$ with $(M^x_a)^* = M^x_a$, $M^x_a M^x_a = M^x_a$ and $\sum_a M^x_a = 1$ for every $x$. The tracial value is
--   $\mathrm{tracialValue}\ G\ \tau\ P = \sum_{x, y, a, b} \mu(x, y)\,[D(x, y, a, b)]\,\mathrm{Re}\,\tau(M^x_a M^y_b)$. Then
--
--   $$\mathrm{tracialValue}\ G\ \tau\ P \;\le\; 1 .$$
--
--   The synchronous value (the instantiation at $\mathcal{A} = \mathbb{C}^{d \times d}$ with the normalized trace) and the commuting-operator value are both instances of the tracial value, so this one inequality gives `SyncStrategy.value_le_one`, `syncValue_le_one` and the bounded-above-ness that the suprema defining the values require.
--
--   **Formalization Note** The generality is a star ring with a complex module structure, not a C*-algebra. The definition takes the real part of $\tau(M^x_a M^y_b)$ so that it carries no proof obligation. `G`, `τ` and `P` are explicit arguments; `X`, `A`, `𝒜` and their instances are section variables, and the proposition is `MIPRE.tracialValue_le_one`.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Games.lean#L499-L528

import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Matrix.Order
import Mathlib.Data.ENat.Lattice
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Definitions.Def_MIPRE_Foundations_Games

open MIPRE
open ComplexOrder Kronecker Matrix
open scoped MatrixOrder
variable {X Y A B : Type*} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
variable {𝒜 ℬ : Type*} [Ring 𝒜] [StarRing 𝒜] [Module ℂ 𝒜]
  [Ring ℬ] [StarRing ℬ] [Module ℂ ℬ]
variable [DecidableEq A]

theorem MIPRE.tracialValue_le_one (G : SynchronousGame X A) (τ : TracialState 𝒜)
    (P : ProjectiveMeasurement X A 𝒜) : tracialValue G τ P ≤ 1 := by sorry
