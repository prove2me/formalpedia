-- Prove2me | Theorems.Thm_OAI_Problem346_symmetric_multilinear_eq_zero_of_diagonal
-- name    : OAI.Problem346.symmetric_multilinear_eq_zero_of_diagonal
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T16:51:49.800538+00:00
-- url     : https://prove2.me/theorems/73a6427b-593c-4a8e-8b2d-14d329cde362
-- title:
--   Polarization: a symmetric multilinear form vanishing on the diagonal is zero
-- statement:
--   Let $W$ be a complex vector space (of arbitrary dimension and without any topology) and let $n\in\mathbb{N}$. Let $T\colon W^n\to\mathbb{C}$ be a multilinear form that is symmetric, i.e. $T(x_{\sigma(1)},\dots,x_{\sigma(n)})=T(x_1,\dots,x_n)$ for every permutation $\sigma$ of $\{1,\dots,n\}$ and all $x_1,\dots,x_n\in W$.
--
--   **Theorem.** If $T$ vanishes on the diagonal, then $T$ is identically zero:
--
--   $$\Big(T(x,x,\dots,x)=0\ \text{ for all } x\in W\Big)\quad\Longrightarrow\quad T(x_1,\dots,x_n)=0\ \text{ for all } x_1,\dots,x_n\in W .$$
--
--   A symmetric multilinear form over $\mathbb{C}$ is thus determined by the homogeneous polynomial $x\mapsto T(x,\dots,x)$ of degree $n$; this is the classical polarization principle, which works because $n!$ is invertible in $\mathbb{C}$. Stated purely algebraically, it applies to forms on infinite-dimensional spaces, for example to a functional on a symmetric power composed with the product map, which is how it is used to show that pure powers span symmetric powers.
--
--   **Formalization Note** Arguments are indexed by `Fin n`; $T$ is a `MultilinearMap ℂ (fun _ : Fin n => W) ℂ`, and symmetry is the hypothesis `T (fun i => x (σ i)) = T x` for all `σ : Equiv.Perm (Fin n)`. The case $n=0$ is included (then $T$ is a constant and the hypothesis says it is $0$).
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/RepresentationTheory/FoulkesHowe/DiagonalPolarization.lean#L26-L56

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
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_FirstLabels
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_FlattenedForm
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_MultilinearPolynomial
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_BlockWeight
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_FirstPolynomial
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_PolynomialShift
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_FirstCounts
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_SlotDerivative
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_TransferEndpoints

open OAI OAI.Problem346
open scoped BigOperators

theorem OAI.Problem346.symmetric_multilinear_eq_zero_of_diagonal
    {W : Type*} [AddCommGroup W] [Module ℂ W] {n : ℕ}
    (T : MultilinearMap ℂ (fun _ : Fin n => W) ℂ)
    (hsym : ∀ (σ : Equiv.Perm (Fin n)) (x : Fin n → W),
      T (fun i => x (σ i)) = T x)
    (hdiag : ∀ x : W, T (fun _ => x) = 0) : T = 0 := by sorry
