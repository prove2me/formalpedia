-- Prove2me | Theorems.Thm_MasulloRH_compact_window_theta_annihilator
-- name    : MasulloRH.compact_window_theta_annihilator
-- status  : Proved
-- author  : @marozols
-- created : 2026-11-21T00:57:38.927434+00:00
-- url     : https://prove2.me/theorems/59ebd27f-4199-4dc1-95c1-ca712b03c7aa
-- title:
--   An analytic annihilator has only finite-order jets in each compact frequency window
-- statement:
--   Let $G:\mathbb R\to\mathbb C$ be real analytic and have finite order of vanishing everywhere. Let $u$ be a tempered distribution annihilating every product $Gq$ with $q$ smooth and compactly supported. For any compactly supported smooth window $b$, the set $S=\{a\in\operatorname{supp}b:G(a)=0\}$ is finite. There are constants $c_{a,k}$ such that every Schwartz function $f$ satisfies
--   $$
--   u(bf)=\sum_{a\in S}\sum_{0\le k<\operatorname{ord}_aG}c_{a,k}\,f^{(k)}(a).
--   $$
--   This describes the possible spectral distributions inside one compact frequency window. The derivative orders are controlled by the actual zeros of the multiplier.
-- source:
--   A. Connes, Trace formula in noncommutative geometry and the zeros of the Riemann zeta function, Appendix I, preprint pp. 65–66, equations (24), (27)–(29), https://arxiv.org/abs/math/9811068. Real-line compact-window version for the spectral synthesis in A. M. Masullo §10.2.1.1; see also the proposal of Calvin Yost-Wolff, Prove2Me discussion d8680fb7-dd35-4a9c-ab4e-5888ec240d48.

import Mathlib
open Set Filter
open scoped ContDiff Topology SchwartzMap BigOperators

theorem MasulloRH.compact_window_theta_annihilator {G : ℝ → ℂ} (hG : ∀ x, AnalyticAt ℝ G x)
    (hfin : ∀ x, analyticOrderAt G x ≠ ⊤)
    (u : 𝓢(ℝ,ℂ) →L[ℂ] ℂ)
    (hann : ∀ q t : 𝓢(ℝ,ℂ), HasCompactSupport (q:ℝ→ℂ) →
      (∀ x, t x = G x * q x) → u t = 0)
    (b : 𝓢(ℝ,ℂ)) (hb : HasCompactSupport (b:ℝ→ℂ)) :
    ∃ S : Finset ℝ, (∀ x, x ∈ S ↔ x ∈ tsupport (b:ℝ→ℂ) ∧ G x = 0) ∧
      ∃ c : (a : S) → Fin (analyticOrderNatAt G a.val) → ℂ,
        ∀ f : 𝓢(ℝ,ℂ), u (SchwartzMap.smulLeftCLM ℂ (b:ℝ→ℂ) f) =
          ∑ a : S, ∑ k : Fin (analyticOrderNatAt G a.val), c a k * iteratedDeriv k.val f a.val := by sorry
