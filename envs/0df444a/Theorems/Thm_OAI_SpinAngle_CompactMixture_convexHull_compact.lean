-- Prove2me | Theorems.Thm_OAI_SpinAngle_CompactMixture_convexHull_compact
-- name    : OAI.SpinAngle.CompactMixture.convexHull_compact
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T07:14:58.461819+00:00
-- url     : https://prove2.me/theorems/500bf100-4205-4106-81a4-cc2d18370901
-- title:
--   The convex hull of a compact set in a finite-dimensional real normed space is compact
-- statement:
--   Let $E$ be a finite-dimensional real normed vector space and let $s\subseteq E$ be a compact set. Its convex hull is the set of all finite convex combinations of points of $s$,
--   $$\operatorname{conv}(s)=\Big\{\sum_{i=1}^{k}w_ix_i\ :\ k\in\mathbb{N},\ x_i\in s,\ w_i\ge0,\ \sum_{i=1}^{k}w_i=1\Big\}.$$
--
--   **Theorem.** $\operatorname{conv}(s)$ is compact.
--
--   This is a standard consequence of Carathéodory's theorem. In the present development it guarantees that the convex hull of a compact set of operators is closed, so that the Haar average of a continuous operator-valued function over a compact group (a twirl) lies in the convex hull of its values and is therefore a finite convex combination of them.
--
--   **Formalization Note** The statement is `IsCompact s → IsCompact (convexHull ℝ s)` for a real normed space `E` with `FiniteDimensional ℝ E`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/RepresentationTheory/SpinAngle/Core.lean#L3368-L3413

import Mathlib
import Definitions.Def_SpinAngle
import Definitions.Def_OAI_RepresentationTheory_SpinAngle_Core

open OAI OAI.SpinAngle
open scoped BigOperators ComplexConjugate InnerProductSpace
open scoped BigOperators ComplexConjugate InnerProductSpace Matrix
open scoped Matrix ComplexOrder
open scoped TensorProduct InnerProductSpace BigOperators
open scoped BigOperators ComplexConjugate
open scoped InnerProductSpace
open scoped TensorProduct InnerProductSpace ComplexOrder
open scoped BigOperators
open scoped InnerProductSpace ComplexOrder BigOperators
open scoped InnerProductSpace BigOperators ComplexOrder
open scoped BigOperators
open scoped BigOperators
open MeasureTheory TopologicalSpace Set
open scoped BigOperators
open scoped BigOperators
open Set
variable {E : Type*} [contextInstance3119_21 : NormedAddCommGroup E] [contextInstance3119_44 : NormedSpace ℝ E] [contextInstance3119_62 : FiniteDimensional ℝ E]

theorem OAI.SpinAngle.CompactMixture.convexHull_compact {s : Set E} (hs : IsCompact s) : IsCompact (convexHull ℝ s) := by sorry
