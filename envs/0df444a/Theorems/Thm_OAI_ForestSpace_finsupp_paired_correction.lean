-- Prove2me | Theorems.Thm_OAI_ForestSpace_finsupp_paired_correction
-- name    : OAI.ForestSpace.finsupp_paired_correction
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T04:16:21.312224+00:00
-- url     : https://prove2.me/theorems/237a7a2d-001e-4c69-845b-4be468202b35
-- title:
--   Paired corrected tests for finitely supported functions on a forest with finite ancestor sets
-- statement:
--   Let $V$ be a partially ordered set (possibly infinite) that is a *forest* (whenever $a\le c$ and $b\le c$, the elements $a,b$ are comparable) and has *finite ancestor sets*: $\{w\in V:\ w\le v\}$ is finite for every $v\in V$. Segments, segment sums $u(S)=\sum_{v\in S}u(v)$ and $\|u\|_{\mathrm{seg}}^2$ (the supremum of $\sum_i u(S_i)^2$ over finite families of pairwise disjoint segments) are as before.
--
--   **Theorem.** Let $H\subseteq V$ be a lower set and let $f,k:V\to\mathbb{R}$ be finitely supported, with $f$ vanishing outside $H$, $k$ vanishing on $H$, $\|f\|_{\mathrm{seg}}^2\le1$ and $\|k\|_{\mathrm{seg}}^2\le1$. Let $s>0$. Then there is a finitely supported $c:V\to\mathbb{R}$ vanishing on $H$ with $\|c\|_{\mathrm{seg}}^2\le1$ such that
--   $$
--   \|f+s(c+k)\|_{\mathrm{seg}}^2\le1+12s^2\qquad\text{and}\qquad\|f+s(c-k)\|_{\mathrm{seg}}^2\le1+12s^2 .
--   $$
--
--   This removes the finiteness assumption on $V$ from the finite-forest version, at the price of the finite-ancestor hypothesis, so that the paired corrected tests are available on the infinite forest underlying the forest space. Only finitely supported vectors are involved; nothing is assumed about the dual space.
--
--   **Formalization Note** Finitely supported functions are `V →₀ ℝ`; "vanishing outside $H$" and "vanishing on $H$" are `SupportedOn f H` and `SupportedOn k Hᶜ`, and the finite-ancestor hypothesis is `(Set.Iic v).Finite` for all `v`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/ForestSpace/Paired.lean#L299-L345

import Mathlib
import Definitions.Def_ForestSpace
import Definitions.Def_OAI_Analysis_ForestSpace_Moduli
import Definitions.Def_OAI_Analysis_ForestSpace_Segments
import Definitions.Def_OAI_Analysis_ForestSpace_FiniteGeometry
import Definitions.Def_OAI_Analysis_ForestSpace_Paired

open OAI OAI.ForestSpace
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
variable {V : Type} [PartialOrder V]

theorem OAI.ForestSpace.finsupp_paired_correction (hF : ForestOrder V)
    (hAnc : ∀ v : V, (Set.Iic v).Finite)
    (H : Set V) (hH : IsLowerSet H) (f k : V →₀ ℝ)
    (hf : SupportedOn f H) (hk : SupportedOn k Hᶜ)
    (hf₁ : TestBound f 1) (hk₁ : TestBound k 1) (s : ℝ) (hs : 0 < s) :
    ∃ c : V →₀ ℝ, SupportedOn c Hᶜ ∧ TestBound c 1 ∧
      TestBound (f + s • (c + k)) (1 + 12 * s ^ 2) ∧
      TestBound (f + s • (c - k)) (1 + 12 * s ^ 2) := by sorry
