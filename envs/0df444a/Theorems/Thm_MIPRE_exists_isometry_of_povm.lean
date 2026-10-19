-- Prove2me | Theorems.Thm_MIPRE_exists_isometry_of_povm
-- name    : MIPRE.exists_isometry_of_povm
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-16T15:22:35.084428+00:00
-- url     : https://prove2.me/theorems/ce11850c-ff96-44b4-9729-3b49ff6f8d94
-- title:
--   Every POVM dilates to an isometry into one extra register
-- statement:
--   Let $d$ and $A$ be finite sets (with decidable equality), $\mathbb{C}^d$ the Hilbert space with orthonormal basis indexed by $d$, and identify $\mathbb{C}^d \otimes \mathbb{C}^A$ with $\mathbb{C}^{d \times A}$. A POVM on $\mathbb{C}^d$ with outcomes in $A$ is a family $E = \{E_a\}_{a \in A}$ of positive semidefinite $d \times d$ complex matrices with $\sum_{a \in A} E_a = 1_d$. For $a \in A$ let $\Pi_a = 1_d \otimes |a\rangle\langle a|$ be the projection of $\mathbb{C}^{d \times A}$ onto the $a$-th slice: the diagonal matrix with entry $1$ at the indices $(p, a')$ with $a' = a$ and $0$ elsewhere; the $\Pi_a$ form a projective measurement on $\mathbb{C}^{d \times A}$.
--
--   For every POVM $\{E_a\}_{a \in A}$ on $\mathbb{C}^d$ there is a matrix $V \in \mathbb{C}^{(d \times A) \times d}$, a linear map $\mathbb{C}^d \to \mathbb{C}^d \otimes \mathbb{C}^A$, such that
--
--   $$V^\dagger V = 1_d \qquad\text{and}\qquad V^\dagger\,\Pi_a\,V = E_a \quad\text{for every } a \in A.$$
--
--   Every POVM is thus the compression of the fixed projective measurement $\{\Pi_a\}_a$ by an isometry into one extra register. This is the first step of the Naimark dilation of a question-indexed family of POVMs (blueprint `lem:naimark-dilation`); the isometry it produces depends on the POVM, and the second step, `exists_unitary_extending`, extends it to a unitary so that one question-independent isometry serves a whole family (`exists_projective_dilation`).
--
--   **Formalization Note** The statement is `∃ V : Matrix (d × A) d ℂ, Vᴴ * V = 1 ∧ ∀ a : A, Vᴴ * (ancillaProj d a * V) = E a` for `E : A → Matrix d d ℂ` implicit, with `hpos : ∀ a, (E a).PosSemidef` (Mathlib's `Matrix.PosSemidef`) and `hsum : ∑ a, E a = 1`; `d A : Type*` with `[Fintype d] [DecidableEq d] [Fintype A] [DecidableEq A]`, neither assumed nonempty. `ancillaProj d a := Matrix.diagonal fun p => if p.2 = a then 1 else 0`, with `ancillaProj_conjTranspose`, `ancillaProj_mul_self` and `sum_ancillaProj` making it a projective measurement. `Vᴴ` is the conjugate transpose. The existential is classical (the witness is not computable from the data).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Dilation.lean#L79-L116; blueprint lem:naimark-dilation

import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Definitions.Def_MIPRE_Foundations_Dilation

open MIPRE
open Matrix
open scoped ComplexOrder Kronecker MatrixOrder

theorem MIPRE.exists_isometry_of_povm {d A : Type*} [Fintype d] [DecidableEq d]
    [Fintype A] [DecidableEq A] {E : A → Matrix d d ℂ}
    (hpos : ∀ a, (E a).PosSemidef) (hsum : ∑ a, E a = 1) :
    ∃ V : Matrix (d × A) d ℂ, Vᴴ * V = 1 ∧
      ∀ a : A, Vᴴ * (ancillaProj d a * V) = E a := by sorry
