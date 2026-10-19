-- Prove2me | Theorems.Thm_MIPRE_exists_unitary_extending
-- name    : MIPRE.exists_unitary_extending
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-16T15:22:39.926375+00:00
-- url     : https://prove2.me/theorems/2ca9e7d5-a33e-4131-852d-1bcacbe27b7b
-- title:
--   An isometry into $\mathbb{C}^d \otimes \mathbb{C}^A$ extends to a unitary agreeing with it on a fixed ancilla slice
-- statement:
--   Let $d$ and $A$ be finite sets (with decidable equality), $a_0 \in A$ a distinguished outcome, and identify $\mathbb{C}^d \otimes \mathbb{C}^A$ with $\mathbb{C}^{d \times A}$. Let $J_{a_0} : \mathbb{C}^d \to \mathbb{C}^{d \times A}$, $v \mapsto v \otimes |a_0\rangle$, be the isometry that pads a vector with the fixed ancilla state $|a_0\rangle$; as a matrix it has entry $1$ at $((j, a_0), j)$ for each $j \in d$ and $0$ elsewhere. Let $V \in \mathbb{C}^{(d \times A) \times d}$ be an isometry, $V^\dagger V = 1_d$.
--
--   Then there is a unitary $U$ on $\mathbb{C}^{d \times A}$ that agrees with $V$ on the $a_0$-slice:
--
--   $$U^\dagger U = 1_{d \times A} \qquad\text{and}\qquad U\,J_{a_0} = V .$$
--
--   This is the step that lets a whole question-indexed family of POVMs be dilated against one fixed state: the isometry produced for each question by `exists_isometry_of_povm` depends on the question, whereas after extension to a unitary $U^x$ the compression $J_{a_0}^\dagger\,(U^x)^\dagger \Pi_a U^x\, J_{a_0} = (V^x)^\dagger \Pi_a V^x$ is along the same $J_{a_0}$ for every question (`exists_projective_dilation`).
--
--   **Formalization Note** The statement is `∃ U : Matrix (d × A) (d × A) ℂ, Uᴴ * U = 1 ∧ U * ancillaEmbed d a₀ = V`, for `a₀ : A` explicit and `V : Matrix (d × A) d ℂ` implicit with `hV : Vᴴ * V = (1 : Matrix d d ℂ)`; `d A : Type*` with `[Fintype d] [DecidableEq d] [Fintype A] [DecidableEq A]`. `ancillaEmbed d a₀ := Matrix.of fun p j => if p = (j, a₀) then 1 else 0`, and `ancillaEmbed_isometry` is `(ancillaEmbed d a₀)ᴴ * ancillaEmbed d a₀ = 1`. Unitarity is asserted as `Uᴴ * U = 1` only. The existential is classical. Blueprint `lem:naimark-dilation`.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Dilation.lean#L136-L187; blueprint lem:naimark-dilation

import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Definitions.Def_MIPRE_Foundations_Dilation

open MIPRE
open Matrix
open scoped ComplexOrder Kronecker MatrixOrder

theorem MIPRE.exists_unitary_extending {d A : Type*} [Fintype d] [DecidableEq d]
    [Fintype A] [DecidableEq A] (a₀ : A) {V : Matrix (d × A) d ℂ}
    (hV : Vᴴ * V = (1 : Matrix d d ℂ)) :
    ∃ U : Matrix (d × A) (d × A) ℂ, Uᴴ * U = 1 ∧ U * ancillaEmbed d a₀ = V := by sorry
