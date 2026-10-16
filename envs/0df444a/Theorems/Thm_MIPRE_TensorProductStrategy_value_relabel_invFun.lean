-- Prove2me | Theorems.Thm_MIPRE_TensorProductStrategy_value_relabel_invFun
-- name    : MIPRE.TensorProductStrategy.value_relabel_invFun
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-15T19:25:21.706221+00:00
-- url     : https://prove2.me/theorems/043f03db-81fa-4be8-bbf6-7fa844f0c2a1
-- title:
--   Playing a strategy of the restricted game on the whole game through retractions of the embeddings keeps the value
-- statement:
--   Let $X, Y, A, B, X', Y'$ be finite types with $X'$ and $Y'$ nonempty. Let $G$ be a game on $(X, Y, A, B)$ (a distribution $\mu$ on $X \times Y$ and a Boolean decision predicate $D$) and $G'$ a game on $(X', Y', A, B)$, and let $e_X : X' \hookrightarrow X$, $e_Y : Y' \hookrightarrow Y$ be embeddings with (i) $G'.\mu\ x'\ y' = G.\mu\ (e_X x')\ (e_Y y')$ for all $x', y'$; (ii) whenever $G.\mu\ x\ y \neq 0$, $x$ is in the image of $e_X$ and $y$ in the image of $e_Y$; (iii) $G'.D\ x'\ y'\ a\ b = G.D\ (e_X x')\ (e_Y y')\ a\ b$ for all $x', y', a, b$. Let $S'$ be a tensor-product strategy for $G'$: dimensions $d_A, d_B$, a unit vector $\psi \in \mathbb{C}^{d_A} \otimes \mathbb{C}^{d_B}$ and projective measurements $\{A^{x'}_a\}$, $\{B^{y'}_b\}$, with value $\sum_{x', y', a, b} \mu'(x', y')\,[D'(x', y', a, b)]\,\mathrm{Re}\,\langle \psi, (A^{x'}_a \otimes B^{y'}_b)\psi\rangle$. Write $r_X = $ `Function.invFun eX` and $r_Y = $ `Function.invFun eY` for retractions of the embeddings (left inverses, chosen with the axiom of choice). The relabeled strategy `S'.relabel G (invFun eX) (invFun eY) (Equiv.refl A) (Equiv.refl B)` is the strategy for $G$ with the same state and the measurements $A^{r_X x}_a$, $B^{r_Y y}_b$. Then
--
--   $$\big(S'.\mathrm{relabel}\ G\ r_X\ r_Y\ \mathrm{id}_A\ \mathrm{id}_B\big).\mathrm{value} \;=\; S'.\mathrm{value} .$$
--
--   This is the other half of `quantumValue_restrictQuestions`: with `value_relabel_of_support` it shows that a game whose question distribution is supported on the image of two embeddings has the quantum value of its restriction to $X' \times Y'$.
--
--   **Formalization Note** `Function.invFun` needs `Nonempty X'` and `Nonempty Y'`, which is why these instance arguments appear; it is noncomputable and takes an arbitrary value off the image. The answer equivalences are `Equiv.refl`. Hypothesis (ii) is `∀ x y, G.μ x y ≠ 0 → (∃ x', eX x' = x) ∧ (∃ y', eY y' = y)`. The value uses the Kronecker product `⊗ₖ` and takes the real part of the inner product. `X'`, `Y'`, `G'` are implicit; `S'`, `G`, `eX`, `eY` are explicit.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/GameRestrict.lean#L70-L107

import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Matrix.Order
import Mathlib.Data.ENat.Lattice
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_GameTransport

open MIPRE
open MIPRE.TensorProductStrategy
open Matrix Kronecker
open scoped ComplexOrder
variable {X Y A B : Type*} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

theorem MIPRE.TensorProductStrategy.value_relabel_invFun {X' Y' : Type*} [Fintype X'] [Fintype Y'] [Nonempty X']
    [Nonempty Y'] {G' : Game X' Y' A B} (S' : TensorProductStrategy G') (G : Game X Y A B)
    (eX : X' ↪ X) (eY : Y' ↪ Y)
    (hμ : ∀ x' y', G'.μ x' y' = G.μ (eX x') (eY y'))
    (hμ0 : ∀ x y, G.μ x y ≠ 0 → (∃ x', eX x' = x) ∧ (∃ y', eY y' = y))
    (hD : ∀ x' y' a b, G'.D x' y' a b = G.D (eX x') (eY y') a b) :
    (S'.relabel G (Function.invFun eX) (Function.invFun eY) (Equiv.refl A)
      (Equiv.refl B)).value = S'.value := by sorry
