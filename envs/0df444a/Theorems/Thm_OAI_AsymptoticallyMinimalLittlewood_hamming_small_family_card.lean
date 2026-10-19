-- Prove2me | Theorems.Thm_OAI_AsymptoticallyMinimalLittlewood_hamming_small_family_card
-- name    : OAI.AsymptoticallyMinimalLittlewood.hamming_small_family_card
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T04:40:21.380804+00:00
-- url     : https://prove2.me/theorems/e20dc501-28fa-491c-a342-e0e7a4fcd5f5
-- title:
--   A Hamming ball of radius $n/16$ in the $n$-cube has at most $e^{3n/8}$ points
-- statement:
--   Let $K$ be a finite set with $n=|K|$ elements. For Boolean vectors $x,y\in\{\mathrm{true},\mathrm{false}\}^{K}$ let $d_H(x,y)=\#\{k\in K: x_k\neq y_k\}$ be their Hamming distance. Let $x\in\{\mathrm{true},\mathrm{false}\}^K$ and let $G$ be a finite set of Boolean vectors such that $d_H(x,y)\le n/16$ for every $y\in G$. Then
--
--   $$
--   |G|\le e^{3n/8}.
--   $$
--
--   Since $3/8<\log 2$, a Hamming ball of radius $n/16$ is an exponentially small part of the cube $\{\mathrm{true},\mathrm{false}\}^K$, which has $2^n=e^{n\log 2}$ points. This is used to show that a large family of signings cannot be covered by few small balls, so two members far apart in Hamming distance can be found.
--
--   **Formalization Note** The center $x$ need not belong to $G$; distances are `hammingDist` cast to $\mathbb{R}$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Littlewood/Rounding.lean#L228-L268

import Mathlib
import Definitions.Def_AsymptoticallyMinimalLittlewood
import Definitions.Def_OAI_Analysis_Littlewood_Gaussian
import Definitions.Def_OAI_Analysis_Littlewood_Rounding

open OAI OAI.AsymptoticallyMinimalLittlewood
universe u v w
open MeasureTheory Complex Real FourierTransform Filter Topology
open scoped FourierTransform SchwartzMap ContDiff

theorem OAI.AsymptoticallyMinimalLittlewood.hamming_small_family_card {α : Type u} [Fintype α] [DecidableEq α]
    (G : Finset (α → Bool)) (x : α → Bool)
    (hG : ∀ y ∈ G, (hammingDist x y : ℝ) ≤ (Fintype.card α : ℝ) / 16) :
    (G.card : ℝ) ≤ Real.exp (3 * Fintype.card α / 8) := by sorry
