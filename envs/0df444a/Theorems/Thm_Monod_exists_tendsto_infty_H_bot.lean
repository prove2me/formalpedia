-- Prove2me | Theorems.Thm_Monod_exists_tendsto_infty_H_bot
-- name    : Monod.exists_tendsto_infty_H_bot
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-30T13:30:32.59886+00:00
-- url     : https://prove2.me/theorems/e68c2fd0-7ce0-4356-8e04-6218c2928b5c
-- title:
--   Lemma 16 — sequences in H(ℤ) pushing everything but one point to ∞
-- statement:
--   For every real $p$ there is a sequence $(g_n)$ in $H(\mathbf{Z})$ such that for every compact $C \subseteq \mathbf{P}^1$ not containing $p$ and every neighbourhood $V$ of $\infty$, eventually $g_n(C) \subseteq V$: $g_n q \to \infty$ uniformly on compact subsets of $\mathbf{P}^1 \setminus \{p\}$.
-- source:
--   Monod, N., Groups of piecewise projective homeomorphisms, Proc. Natl. Acad. Sci. USA 110 (2013) 4524–4527, https://doi.org/10.1073/pnas.1218426110 (arXiv:1209.5229v2, whose page numbers are used), p. 3, Lemma 16

import Mathlib
import Definitions.Def_Monod_PiecewiseProjective

namespace Monod

theorem exists_tendsto_infty_H_bot (p : ℝ) :
    ∃ g : ℕ → H ⊥, ∀ C : Set (OnePoint ℝ), IsCompact C → (p : OnePoint ℝ) ∉ C →
      ∀ V ∈ nhds OnePoint.infty, ∀ᶠ n in Filter.atTop, ∀ q ∈ C, (g n : OnePoint ℝ ≃ₜ OnePoint ℝ) q ∈ V := by
  sorry

end Monod
