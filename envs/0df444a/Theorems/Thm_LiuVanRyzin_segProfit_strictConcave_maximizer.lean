-- Prove2me | Theorems.Thm_LiuVanRyzin_segProfit_strictConcave_maximizer
-- name    : LiuVanRyzin.segProfit_strictConcave_maximizer
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T15:38:26.087651+00:00
-- url     : https://prove2.me/theorems/1c173bb5-f5a2-4fa5-8c21-2451fab5914b
-- title:
--   Lemma 1 — $\Pi(v)$ is strictly concave on $v\ge p_1$; its maximizer on $[p_1,\bar U]$ is $v^0$ if $v^0\le\bar U$, else $\bar U$
-- statement:
--   Let $N>0$, $\bar U>0$, $\alpha<p_2<p_1$ and $0<\gamma<1$, and let
--   $$\Pi(v)=\frac{N}{\bar U}\left((p_1-\alpha)(\bar U-v)+(p_2-\alpha)(v-p_2)\left(\frac{v-p_1}{v-p_2}\right)^\gamma\right)$$
--   be the segmented-market profit (6). Then
--
--   1. $\Pi$ is strictly concave on $[p_1,\infty)$;
--   2. if $v^0>p_1$ solves the first-order condition (7) and $p_1\le\bar U$, then the point
--   $$v^*=\begin{cases}v^0,& v^0\le\bar U,\\ \bar U,&\text{otherwise,}\end{cases}$$
--   lies in $[p_1,\bar U]$ and maximizes $\Pi$ over $[p_1,\bar U]$.
--
--   Together with the uniqueness of the root of (7), this identifies the segmented-market optimum $\Pi^0$ that Proposition 3 compares with the low-price-only profit.
--
--   **Formalization Note** The paper uses $p_1\le\bar U$ without stating it: (6) maximizes over $\bar U\ge v\ge p_1$, which needs a nonempty interval. $\bar U>0$ is part of §3's uniform law on $[0,\bar U]$. Uniqueness of the maximizer follows from part 1 and is not restated.
-- source:
--   Liu, van Ryzin, Strategic Capacity Rationing to Induce Early Purchases, Management Science 54(6):1115–1131 (2008), p. 1122, Lemma 1

import Mathlib
import Definitions.Def_LiuVanRyzin_PowerModel

namespace LiuVanRyzin

/-- Lemma 1 (Liu–van Ryzin 2008, p. 1122). The profit `Π(v)` of (6) is strictly concave in
`v ≥ p₁`, and its maximizer over `p₁ ≤ v ≤ Ū` is the root `v⁰` of (7) if `v⁰ ≤ Ū`, and `Ū`
otherwise. -/
theorem segProfit_strictConcave_maximizer (N Ubar p₁ p₂ α γ : ℝ) (hN : 0 < N)
    (hU : 0 < Ubar) (hα : α < p₂) (hp : p₂ < p₁) (hγ0 : 0 < γ) (hγ1 : γ < 1) :
    StrictConcaveOn ℝ (Set.Ici p₁) (segProfit N Ubar p₁ p₂ α γ) ∧
      ∀ v₀ : ℝ, p₁ < v₀ → focLHS p₁ p₂ α γ v₀ = 0 → p₁ ≤ Ubar →
        (if v₀ ≤ Ubar then v₀ else Ubar) ∈ Set.Icc p₁ Ubar ∧
          IsMaxOn (segProfit N Ubar p₁ p₂ α γ) (Set.Icc p₁ Ubar)
            (if v₀ ≤ Ubar then v₀ else Ubar) := by sorry

end LiuVanRyzin
