-- Prove2me | Theorems.Thm_MIPRE_exists_projective_dilation
-- name    : MIPRE.exists_projective_dilation
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-16T15:22:43.142482+00:00
-- url     : https://prove2.me/theorems/36d5ec00-b305-4132-8d74-a8e999f9d9db
-- title:
--   Naimark dilation of a question-indexed POVM family against a fixed ancilla state
-- statement:
--   Let $d$ and $A$ be finite sets (with decidable equality), $X$ an arbitrary set of questions, and $a_0 \in A$. Let $\{E^x_a\}_{x \in X,\, a \in A}$ be a question-indexed family of POVMs on $\mathbb{C}^d$: for every $x$, each $E^x_a$ is a positive semidefinite $d \times d$ complex matrix and $\sum_{a \in A} E^x_a = 1_d$. Identify $\mathbb{C}^d \otimes \mathbb{C}^A$ with $\mathbb{C}^{d \times A}$ and let $J_{a_0} : \mathbb{C}^d \to \mathbb{C}^{d \times A}$, $v \mapsto v \otimes |a_0\rangle$, be the isometry padding a vector with the fixed ancilla state $|a_0\rangle$.
--
--   Then there is a family $\{P^x_a\}_{x \in X,\, a \in A}$ of matrices on $\mathbb{C}^{d \times A}$ such that for every $x$ the family $\{P^x_a\}_a$ is a projective measurement, each $P^x_a$ being self-adjoint and idempotent with $\sum_a P^x_a = 1$, and every $E^x_a$ is the compression of $P^x_a$ by the single, question-independent isometry $J_{a_0}$:
--
--   $$J_{a_0}^\dagger\, P^x_a\, J_{a_0} \;=\; E^x_a \qquad\text{for all } x \in X \text{ and } a \in A.$$
--
--   That the compressing isometry does not depend on $x$ is what allows the dilation to be applied to one shared state: a strategy using POVMs on a state $\psi$ becomes one using projective measurements on $\psi \otimes |a_0\rangle$, with the same outcome probabilities for every question. The lemma is the substantive step of `lem:povm-value-eq` (mixed states and POVMs do not change the quantum value), and it is reused by `lem:ms-direct-anticomm`, which dilates the Magic Square's six constraint POVMs against one shared ancilla.
--
--   **Formalization Note** The statement is `∃ P : X → A → Matrix (d × A) (d × A) ℂ, (∀ x a, star (P x a) = P x a) ∧ (∀ x a, P x a * P x a = P x a) ∧ (∀ x, ∑ a, P x a = 1) ∧ (∀ x a, (ancillaEmbed d a₀)ᴴ * (P x a * ancillaEmbed d a₀) = E x a)`, for `E : X → A → Matrix d d ℂ` implicit with `hpos : ∀ x a, (E x a).PosSemidef` and `hsum : ∀ x, ∑ a, E x a = 1`, and `a₀ : A` explicit; `star` on complex matrices is the conjugate transpose. `d A X : Type*`, with `[Fintype d] [DecidableEq d] [Fintype A] [DecidableEq A]` and no assumption on `X`, which need not be finite; the nonemptiness of `A` is carried by the explicit `a₀`. `ancillaEmbed d a₀ := Matrix.of fun p j => if p = (j, a₀) then 1 else 0`. The existential is classical. Blueprint `lem:naimark-dilation`, which lists this with `exists_isometry_of_povm` and `exists_unitary_extending`.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Dilation.lean#L189-L226; blueprint lem:naimark-dilation

import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Definitions.Def_MIPRE_Foundations_Dilation

open MIPRE
open Matrix
open scoped ComplexOrder Kronecker MatrixOrder

theorem MIPRE.exists_projective_dilation {d A X : Type*} [Fintype d] [DecidableEq d]
    [Fintype A] [DecidableEq A] (a₀ : A) {E : X → A → Matrix d d ℂ}
    (hpos : ∀ x a, (E x a).PosSemidef) (hsum : ∀ x, ∑ a, E x a = 1) :
    ∃ P : X → A → Matrix (d × A) (d × A) ℂ,
      (∀ x a, star (P x a) = P x a) ∧
      (∀ x a, P x a * P x a = P x a) ∧
      (∀ x, ∑ a, P x a = 1) ∧
      (∀ x a, (ancillaEmbed d a₀)ᴴ * (P x a * ancillaEmbed d a₀) = E x a) := by sorry
