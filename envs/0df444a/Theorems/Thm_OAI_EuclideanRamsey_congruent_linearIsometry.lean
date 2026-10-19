-- Prove2me | Theorems.Thm_OAI_EuclideanRamsey_congruent_linearIsometry
-- name    : OAI.EuclideanRamsey.congruent_linearIsometry
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T01:53:33.216348+00:00
-- url     : https://prove2.me/theorems/705b29cb-e391-4fb4-b3ba-41416c34eca9
-- title:
--   Congruent copies of an affinely spanning configuration are images under an isometric affine map
-- statement:
--   Let $s,d,D\in\mathbb{N}$, let $a_0,\dots,a_{s-1}$ be points of Euclidean space $\mathbb{R}^d$ and $b_0,\dots,b_{s-1}$ points of $\mathbb{R}^D$, and let an index $i_0\in\{0,\dots,s-1\}$ be given. Assume that the affine span of $\{a_0,\dots,a_{s-1}\}$ is all of $\mathbb{R}^d$ and that $b$ is congruent to $a$, i.e. $\|b_i-b_j\|=\|a_i-a_j\|$ for all $i,j$. Then there exist a linear isometry $Q:\mathbb{R}^d\to\mathbb{R}^D$ (a linear map with $\|Qx\|=\|x\|$ for all $x$) and a vector $t\in\mathbb{R}^D$ such that
--   $$b_i=t+Q\,a_i\qquad\text{for all } i\in\{0,\dots,s-1\}.$$
--
--   Thus every congruent copy of a full-dimensional configuration, even inside a higher-dimensional space, is the image of the configuration under an isometric affine embedding. This rigidity lets a monochromatic congruent copy in $\mathbb{R}^D$ be written explicitly as $t+Qa$, so that functions evaluated along the copy can be expanded through the rows of $Q$.
--
--   **Formalization Note** Points live in `Space d = EuclideanSpace ℝ (Fin d)`, congruence `Congruent a b` is stated with `dist`, the span hypothesis is `affineSpan ℝ (Set.range a) = ⊤`, and `Q : Space d →ₗᵢ[ℝ] Space D`. The index `i₀` is an explicit argument that does not appear in the conclusion; the span hypothesis already forces $s\ge 1$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/EuclideanRamsey/Congruence.lean#L74-L97

import Mathlib
import Definitions.Def_EuclideanRamsey

open OAI OAI.EuclideanRamsey
universe uIndex uDomain uCodomain
open scoped TensorProduct RealInnerProductSpace

theorem OAI.EuclideanRamsey.congruent_linearIsometry {s d D : ℕ} (a : Fin s → Space d)
    (b : Fin s → Space D) (i₀ : Fin s)
    (hspan : affineSpan ℝ (Set.range a) = ⊤) (h : Congruent a b) :
    ∃ Q : Space d →ₗᵢ[ℝ] Space D, ∃ t : Space D, ∀ i, b i = t + Q (a i) := by sorry
