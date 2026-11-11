-- Prove2me | Theorems.Thm_IntervalExplore_KT1_theorem_6
-- name    : IntervalExplore.KT1.theorem_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:10:35.803371+00:00
-- url     : https://prove2.me/theorems/bc94ad68-1627-4420-afd2-444ba4ca1ef1
-- title:
--   Theorem 6 — the Moore edge bound from girth
-- statement:
--   Let $g\ge1$ be an integer and let $G'=(V',E')$ be any finite simple undirected graph whose girth is at least $2g+1$. The girth of an acyclic graph is infinite. Then
--   $$
--   |E'|\le \frac12|V'|^{1+1/g}+\frac12|V'|.
--   $$
--   This is Theorem 6 as quoted in the source from Füredi and Simonovits, Theorem 4.1. It supplies the extremal graph inequality used by the edge-charge bounds, and requires neither regularity nor connectivity.
--
--   Differences from the source:
--   - encoding: girth with value infinity on acyclic graphs and the real power |V′|^{1+1/g} → Mathlib egirth in extended naturals and Real.rpow; reason: this preserves acyclic graphs and the fractional exponent; g≥1 excludes division by zero
-- source:
--   Yuichi Sudo, Naoki Kitamura, Masahiro Shibata, Junya Nakamura, Sébastien Tixeuil, Toshimitsu Masuzawa, Koichi Wada, STOC 2027 submission #1589 (October 2026), Theorem 6 (Theorem 4.1 in [FS13]), p.8 (PDF p.9)

import Definitions.Def_IntervalExplore_KT1_Rates

set_option autoImplicit false

namespace IntervalExplore.KT1

/-- Theorem 6, p.8 (PDF p.9), the Moore bound quoted as [FS13, Theorem 4.1]. -/
theorem theorem_6 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (g : ℕ) (hg : 1 ≤ g) (hgirth : ((2 * g + 1 : ℕ) : ℕ∞) ≤ G.egirth) :
    (edgeCount G : ℝ) ≤ (1 / 2 : ℝ) * (Fintype.card V : ℝ) ^ (1 + 1 / (g : ℝ)) +
      (1 / 2 : ℝ) * Fintype.card V := by sorry

end IntervalExplore.KT1
