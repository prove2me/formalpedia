-- Prove2me | Theorems.Thm_MIPRE_TensorProductStrategy_value_relabel_of_support
-- name    : MIPRE.TensorProductStrategy.value_relabel_of_support
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-15T19:25:28.655841+00:00
-- url     : https://prove2.me/theorems/84e20e2a-9d00-496d-8dab-48838c0ff13b
-- title:
--   Playing a tensor-product strategy on the restriction of a game to the support of its questions keeps the value
-- statement:
--   Let $X, Y, A, B, X', Y'$ be finite types. A game $G$ on $(X, Y, A, B)$ consists of a probability distribution $\mu$ on $X \times Y$ and a decision predicate $D : X \to Y \to A \to B \to \mathrm{Bool}$. Let $G'$ be a game on $(X', Y', A, B)$ with the same answer alphabets, and $e_X : X' \hookrightarrow X$, $e_Y : Y' \hookrightarrow Y$ embeddings such that (i) $G'.\mu\ x'\ y' = G.\mu\ (e_X x')\ (e_Y y')$ for all $x', y'$; (ii) whenever $G.\mu\ x\ y \neq 0$, $x$ is in the image of $e_X$ and $y$ in the image of $e_Y$; (iii) $G'.D\ x'\ y'\ a\ b = G.D\ (e_X x')\ (e_Y y')\ a\ b$ for all $x', y', a, b$. A tensor-product strategy $S$ for $G$ consists of dimensions $d_A, d_B$, a unit vector $\psi \in \mathbb{C}^{d_A} \otimes \mathbb{C}^{d_B}$ and projective measurements $\{A^x_a\}_a$ on $\mathbb{C}^{d_A}$ and $\{B^y_b\}_b$ on $\mathbb{C}^{d_B}$; its value is $\sum_{x, y, a, b} \mu(x, y)\,[D(x, y, a, b)]\, \mathrm{Re}\,\langle \psi, (A^x_a \otimes B^y_b)\psi\rangle$. The relabeled strategy `S.relabel G' eX eY (Equiv.refl A) (Equiv.refl B)` is the strategy for $G'$ with the same state and the measurements $A^{e_X x'}_a$ and $B^{e_Y y'}_b$. Then
--
--   $$\big(S.\mathrm{relabel}\ G'\ e_X\ e_Y\ \mathrm{id}_A\ \mathrm{id}_B\big).\mathrm{value} \;=\; S.\mathrm{value} .$$
--
--   This is one half of `quantumValue_restrictQuestions`: a game whose question distribution is supported on the image of two embeddings has the quantum value of its restriction. Its consumer is the class verifier of the polynomial-time halting reduction, whose game has every string of length at most $B$ as a question while its sampler only produces strings of one fixed length.
--
--   **Formalization Note** `relabel` accepts arbitrary maps on the questions and equivalences on the answers; here the answer equivalences are `Equiv.refl A` and `Equiv.refl B`. Hypothesis (ii) is `∀ x y, G.μ x y ≠ 0 → (∃ x', eX x' = x) ∧ (∃ y', eY y' = y)`. The value is the real part of a complex inner product computed with the Kronecker product `⊗ₖ` of matrices. No `Nonempty` instances are assumed, in contrast with `value_relabel_invFun`. `X'`, `Y'`, `G` are implicit; `S`, `G'`, `eX`, `eY` explicit.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/GameRestrict.lean#L34-L68

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

theorem MIPRE.TensorProductStrategy.value_relabel_of_support {X' Y' : Type*} [Fintype X'] [Fintype Y'] {G : Game X Y A B}
    (S : TensorProductStrategy G) (G' : Game X' Y' A B) (eX : X' ↪ X) (eY : Y' ↪ Y)
    (hμ : ∀ x' y', G'.μ x' y' = G.μ (eX x') (eY y'))
    (hμ0 : ∀ x y, G.μ x y ≠ 0 → (∃ x', eX x' = x) ∧ (∃ y', eY y' = y))
    (hD : ∀ x' y' a b, G'.D x' y' a b = G.D (eX x') (eY y') a b) :
    (S.relabel G' eX eY (Equiv.refl A) (Equiv.refl B)).value = S.value := by sorry
