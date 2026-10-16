-- Prove2me | Theorems.Thm_MIPRE_SyncStrategy_value_const
-- name    : MIPRE.SyncStrategy.value_const
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-15T19:25:31.597012+00:00
-- url     : https://prove2.me/theorems/ccf3cfe4-fb2d-4930-8c12-da92ebbf1c40
-- title:
--   The value of the constant synchronous strategy is the acceptance mass of its fixed answer pair
-- statement:
--   Let $X$ and $A$ be finite types, with decidable equality on $A$, and $G$ a synchronous game on $(X, A)$: a probability distribution $\mu$ on $X \times X$ and a decision predicate $D : X \to X \to A \to A \to \mathrm{Bool}$ with $D(x, x, a, b) = \mathrm{false}$ whenever $a \neq b$. A synchronous strategy for $G$ is a dimension $d > 0$ together with a question-indexed projective measurement $\{M^x_a\}$ on $\mathbb{C}^{d}$ (self-adjoint idempotents summing to the identity for each $x$); its value is $\sum_{x, y, a, b} \mu(x, y)\,[D(x, y, a, b)]\,\mathrm{Re}\,\mathrm{Tr}(M^x_a M^y_b)/d$. For $a_0 \in A$, the constant strategy `const G a₀` has $d = 1$ and $M^x_a = 1$ if $a = a_0$ and $0$ otherwise, for every question $x$. Then
--
--   $$(\mathrm{const}\ G\ a_0).\mathrm{value} \;=\; \sum_{x \in X}\ \sum_{y \in X} \mu(x, y)\cdot [D(x, y, a_0, a_0)],$$
--
--   where $[\cdot]$ is $1$ for `true` and $0$ for `false`.
--
--   Together with `isPCC_const` (the constant strategy is PCC) this gives `Verifier.hasPerfectPCC_of_accepts_diagonal`: a decider that accepts a fixed answer on every question pair has a value-$1$ PCC strategy, the trivial strategy behind the "yes" instance of the halting reduction's classes.
--
--   **Formalization Note** `SyncStrategy.value` is `tracialValue G (normalizedTrace (Fin d)) P`, the generic tracial value against the dimension-normalized trace, and `value_eq` writes it out as the sum above. The right-hand side is a finite real sum of `G.μ x y * (if G.D x y a₀ a₀ then 1 else 0)`. The game `G` is an explicit argument here (elsewhere in the file it is a section variable), and the proposition is `MIPRE.SyncStrategy.value_const`.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/GameTransport.lean#L520-L540

import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Matrix.Order
import Mathlib.Data.ENat.Lattice
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_GameTransport

open MIPRE
open MIPRE.SyncStrategy
open Matrix Kronecker
open scoped ComplexOrder
variable {X Y A B : Type*} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
variable [DecidableEq A] {G : SynchronousGame X A}

theorem MIPRE.SyncStrategy.value_const (G : SynchronousGame X A) (a₀ : A) :
    (const G a₀).value = ∑ x, ∑ y, G.μ x y * (if G.D x y a₀ a₀ then 1 else 0) := by sorry
