-- Prove2me | Theorems.Thm_OAI_GAD_posDef_fromBlocks_zero
-- name    : OAI.GAD.posDef_fromBlocks_zero
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T22:13:41.349603+00:00
-- url     : https://prove2.me/theorems/4281eaed-0e58-4b0d-a4dc-a3b6ee18cde4
-- title:
--   A block-diagonal matrix with positive definite diagonal blocks is positive definite
-- statement:
--   Let $\iota$ and $\kappa$ be finite index sets and let $D\in\mathbb{C}^{\iota\times\iota}$ and $E\in\mathbb{C}^{\kappa\times\kappa}$ be positive definite. Then the block-diagonal matrix indexed by the disjoint union $\iota\sqcup\kappa$,
--
--   $$
--   D\oplus E=\begin{pmatrix}D&0\\0&E\end{pmatrix}\in\mathbb{C}^{(\iota\sqcup\kappa)\times(\iota\sqcup\kappa)},
--   $$
--
--   is positive definite.
--
--   Here a complex square matrix $M$ is positive definite when it is Hermitian and $x^{*}Mx>0$ for every nonzero vector $x$. The statement allows block constructions, such as embedding a pair $(D,E)$ of positive definite matrices into one larger matrix, to stay inside the domain of positive definite matrices.
--
--   **Formalization Note** The block matrix is `Matrix.fromBlocks D 0 0 E`, indexed by the sum type `ι ⊕ κ`; no decidable equality on the index types is needed.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/AmplitudeDamping/LogDetConvexity.lean#L111-L136

import Mathlib
import Definitions.Def_AmplitudeDamping
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_Channel
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_MatrixDifferentiation
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_LogDetConvexity

open OAI OAI.GAD
universe u_1 u_2 u_3
open scoped BigOperators
open Matrix
open scoped BigOperators ComplexOrder MatrixOrder
open scoped ComplexOrder MatrixOrder
open Matrix Set
open scoped ComplexOrder MatrixOrder
open Matrix Set
variable {ι : Type u_2} {κ : Type u_3} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

omit [DecidableEq ι] [DecidableEq κ] in
theorem OAI.GAD.posDef_fromBlocks_zero {D : Matrix ι ι ℂ} {E : Matrix κ κ ℂ}
    (hD : D.PosDef) (hE : E.PosDef) :
    (Matrix.fromBlocks D 0 0 E).PosDef := by sorry
