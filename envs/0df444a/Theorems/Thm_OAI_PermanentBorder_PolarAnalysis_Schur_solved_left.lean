-- Prove2me | Theorems.Thm_OAI_PermanentBorder_PolarAnalysis_Schur_solved_left
-- name    : OAI.PermanentBorder.PolarAnalysis.Schur.solved_left
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T22:38:10.062626+00:00
-- url     : https://prove2.me/theorems/e03317bf-0478-4b5b-a38c-2b3b7d70c3ac
-- title:
--   The normalised left kernel vector of a bordered matrix produces its Schur complement
-- statement:
--   Let $\iota$ be a finite index set, $a\in\mathbb{C}$, $\beta,\gamma\in\mathbb{C}^{\iota}$, and let $E\in\mathbb{C}^{\iota\times\iota}$ be a matrix with $\det E\neq0$. Consider the bordered matrix with rows and columns indexed by $\{\ast\}\sqcup\iota$,
--   $$M=\begin{pmatrix}a&\beta^{\top}\\ \gamma&E\end{pmatrix},$$
--   the row vector $\lambda=-\beta^{\top}E^{-1}$ and the Schur complement $s=a-\beta^{\top}E^{-1}\gamma$. Then
--
--   $$
--   \begin{pmatrix}1&\lambda\end{pmatrix}M=\begin{pmatrix}s&0\end{pmatrix},
--   $$
--
--   that is, $a+\lambda\gamma=s$ and $\beta^{\top}+\lambda E=0$.
--
--   Thus the row vector $(1,\lambda)$, normalised to have first entry $1$, annihilates every column of $M$ indexed by $\iota$ and produces the Schur complement $s$ in the first column (recall $\det M=\det E\cdot s$). It is the left-handed companion of the identity $M\,(1,-E^{-1}\gamma)^{\top}=(s,0)^{\top}$; together the two identities are used to differentiate the Schur complement of a matrix family.
--
--   **Formalization Note** The bordered matrix is `block a β γ E`, built with `Matrix.fromBlocks` on the index type `Unit ⊕ ι`; the vector $(1,\lambda)$ is `normalized (left β E)` and $s$ is `scalar a β γ E`. The inverse $E^{-1}$ is Mathlib's total matrix inverse; the hypothesis $\det E\neq0$ is what makes it a genuine inverse.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Algebra/Determinantal/KernelCharts.lean#L412-L427

import Mathlib
import Definitions.Def_SmoothInitialForm
import Definitions.Def_OAI_Algebra_Determinantal_Multigraded
import Definitions.Def_OAI_Algebra_Determinantal_LinearForms
import Definitions.Def_OAI_Algebra_Determinantal_PointBounds
import Definitions.Def_OAI_Algebra_Determinantal_ProjectiveCounts
import Definitions.Def_OAI_Algebra_Determinantal_KernelCharts

open OAI OAI.PermanentBorder OAI.PermanentBorder.PolarAnalysis OAI.PermanentBorder.PolarAnalysis.Schur
open Matrix
open scoped Matrix
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem OAI.PermanentBorder.PolarAnalysis.Schur.solved_left (a : ℂ) (β γ : ι → ℂ) (E : Matrix ι ι ℂ) (hE : E.det ≠ 0) :
    normalized (left β E) ᵥ* block a β γ E =
      Sum.elim (fun _ => scalar a β γ E) (fun _ => 0) := by sorry
