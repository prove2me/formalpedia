-- Prove2me | Theorems.Thm_OAI_Problem346_symmetric_diagonal_mixed_zero
-- name    : OAI.Problem346.symmetric_diagonal_mixed_zero
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T16:31:47.724575+00:00
-- url     : https://prove2.me/theorems/6a542e7d-3d53-475a-8254-90b76a991dd3
-- title:
--   A symmetric form vanishing on the diagonal along an affine line has vanishing first polarization
-- statement:
--   Let $E$ be a complex vector space and $a\in\mathbb{N}$. Let $T\colon E^a\to\mathbb{C}$ be a symmetric multilinear form: $T(v_{\sigma(0)},\dots,v_{\sigma(a-1)})=T(v_0,\dots,v_{a-1})$ for every permutation $\sigma$ of $\{0,\dots,a-1\}$ and every $v\in E^a$. For $x,y\in E$ and $k\in\{0,\dots,a-1\}$ let $x^{(k\leftarrow y)}\in E^a$ be the tuple whose $k$-th entry is $y$ and whose other entries are $x$.
--
--   **Theorem.** Let $x,y\in E$ and $i\in\{0,\dots,a-1\}$ (so in particular $a\ge1$). If
--
--   $$
--   T(x+c\,y,\ x+c\,y,\ \dots,\ x+c\,y)=0\qquad\text{for every }c\in\mathbb{C},
--   $$
--
--   then $T\bigl(x^{(i\leftarrow y)}\bigr)=0$.
--
--   The diagonal value $T(z,\dots,z)$ is a homogeneous polynomial in $z$. The theorem says that if it vanishes along an entire affine line $x+\mathbb{C}y$, then so does its first polarization at $x$ in the direction $y$. In the vanishing argument for the Foulkes map, this is applied to lines in $\operatorname{Sym}^bV$ all of whose points are monomials. Diagonal vanishing at monomials then yields mixed values of the form $T(y,x,\dots,x)=0$.
--
--   **Formalization Note** $T$ is a `MultilinearMap ℂ (fun _ : Fin a => E) ℂ`, symmetry is the hypothesis `∀ σ v, T (fun k => v (σ k)) = T v`, and $x^{(i\leftarrow y)}$ is `Function.update (fun _ => x) i y` with `i : Fin a`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/RepresentationTheory/FoulkesHowe/DiagonalCoefficient.lean#L88-L107

import Mathlib
import Definitions.Def_FoulkesHowe
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_Model
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_DegreeOne
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_Functoriality
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_LinearCase
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_PermanentPairing
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_SymmetricLift
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_AlgebraEvaluation
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_SymmetricDual
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_TensorPresentation
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_FiniteDimension
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_MonomialMultilinear
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_Spanning
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_Actions
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_Naturality
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_DualEmbedding
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_PairingConstruction
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_FoulkesMultilinear
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_CanonicalMap
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_Multiplication
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_VanishingInduction
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_DiagonalCoefficient

open OAI OAI.Problem346
open scoped BigOperators
universe u
variable {E : Type u} [AddCommGroup E] [Module ℂ E]

theorem OAI.Problem346.symmetric_diagonal_mixed_zero {a : ℕ}
    (T : MultilinearMap ℂ (fun _ : Fin a => E) ℂ)
    (hsym : ∀ (σ : Equiv.Perm (Fin a)) (v : Fin a → E),
      T (fun k => v (σ k)) = T v)
    (x y : E) (i : Fin a)
    (h : ∀ c : ℂ, T (fun _ => x + c • y) = 0) :
    T (Function.update (fun _ => x) i y) = 0 := by sorry
