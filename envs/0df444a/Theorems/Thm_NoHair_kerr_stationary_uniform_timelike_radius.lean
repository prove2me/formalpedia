-- Prove2me | Theorems.Thm_NoHair_kerr_stationary_uniform_timelike_radius
-- name    : NoHair.kerr_stationary_uniform_timelike_radius
-- status  : Proved
-- author  : @Igor Valuev
-- created : 2026-11-23T07:24:34.489888+00:00
-- url     : https://prove2.me/theorems/531830ed-261c-40ce-ad16-617aed8bf77d
-- title:
--   Sharp radial cutoff for a uniformly timelike stationary field in vacuum Kerr
-- statement:
--   In positive-radius vacuum Kerr with mass $m>0$ and spin $a$, let $K$ generate stationary time translations in Kerr–Schild coordinates. For any real radial cutoff $R$ and $0\le\delta<1$,
--   $$
--   \bigl[\,g(K,K)<-\delta\text{ throughout }\{r>R\}\,\bigr]
--   \quad\Longleftrightarrow\quad 2m\le(1-\delta)R .
--   $$
--   In particular, strict timelikeness on the whole open radial end is equivalent to $R\ge 2m$.
-- source:
--   M. Visser, The Kerr spacetime: A brief introduction, Section 10, pp. 29–30, equations (132)–(138), https://arxiv.org/abs/0706.0622 . The sharp uniform bound is the equatorial maximum of (136).

import Definitions.Def_NoHair_kerrNewman

open NoHair Set
open scoped ContDiff Manifold

theorem NoHair.kerr_stationary_uniform_timelike_radius (m a R δ : ℝ) (hm : 0 < m) (hδ : 0 ≤ δ ∧ δ < 1)
    (φ : ℝ → kerrNewmanSpacetime a → kerrNewmanSpacetime a)
    (hφ : ∀ s x, (φ s x).val = x.val + s • coordBasis 0)
    (hsym : IsSymmetryFlow (kerrNewmanMetricField m a 0) (kerrNewmanFieldField a 0) φ) :
    (∀ x : kerrNewmanSpacetime a, R < ksRadius a x.val →
      kerrNewmanMetricField m a 0 x (flowGenerator φ x) (flowGenerator φ x) < -δ)
      ↔ 2 * m ≤ (1 - δ) * R := by
  sorry
