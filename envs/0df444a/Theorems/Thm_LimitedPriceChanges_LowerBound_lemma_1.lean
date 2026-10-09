-- Prove2me | Theorems.Thm_LimitedPriceChanges_LowerBound_lemma_1
-- name    : LimitedPriceChanges.LowerBound.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T16:04:56.520003+00:00
-- url     : https://prove2.me/theorems/05fcaf66-2990-45cf-a41a-badda1b3a23b
-- title:
--   Lemma 1, p. 36 — wrong nearest instance incurs regret
-- statement:
--   Fix $m\ge1$ and $T\ge1$. Suppose every constructed parameter $z_\zeta$ lies in $[1/6,5/6]$, and let $\widehat\zeta(p)$ be any selection minimizing $|z_\eta^{-1}-p|$ over $\eta\in\mathcal H$. For every feasible price $p\in[1,6]$ and true sign vector $\zeta$,
--   $$G^*(z_\zeta)-r_{z_\zeta}(p)\ge\frac{|z_{\widehat\zeta(p)}-z_\zeta|^2}{64}.$$
--   The lemma relates an incorrect nearest parameter to one period of regret.
--
--   **Formalization Note** The interval premise is the corrected conclusion of (50). The arg-min is a selection rather than a freely chosen sign vector. The paper's proof contains minor algebraic slips in (52)–(53); the bound above is its stated conclusion.
-- source:
--   Chen, Chao and Wang, Data-Based Dynamic Pricing and Inventory Control with Censored Demand and Limited Price Changes, SSRN 2700747 (revision of 2020-02-10), p. 36, (51), Lemma 1

import Mathlib
import Definitions.Def_LimitedPriceChanges_LowerBound_Hierarchy

namespace LimitedPriceChanges.LowerBound

/-- Lemma 1, p. 36, with the nearest-instance selection of (51). -/
theorem lemma_1 (m T : ℕ) (hm : 1 ≤ m) (hT : 1 ≤ T)
    (hvalid : ∀ ζ : SignVector m, zz m T ζ ∈ Set.Icc (1 / 6 : ℝ) (5 / 6 : ℝ))
    (zsel : ℝ → SignVector m) (hsel : IsNearest m T zsel)
    (p : ℝ) (hp : p ∈ Set.Icc (1 : ℝ) 6) (ζ : SignVector m) :
    |zz m T (zsel p) - zz m T ζ| ^ 2 / 64 ≤
      Gstar (zz m T ζ) - rev p (zz m T ζ) := by sorry

end LimitedPriceChanges.LowerBound
