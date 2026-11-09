-- Prove2me | Theorems.Thm_GevreyGibbsSep_lemma_A_8
-- name    : GevreyGibbsSep.lemma_A_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T16:35:48.543793+00:00
-- url     : https://prove2.me/theorems/9afb03d4-2d2e-4ab5-ae5a-6ddd46847e95
-- title:
--   Lemma A.8 — $|\langle\psi_{\beta+\delta}|\psi_\beta\rangle|\ge1/\cosh(\delta\Delta/4)$
-- statement:
--   Let $|\psi_\beta\rangle$ and $|\psi_{\beta+\delta}\rangle$ be the normalized grid Gibbs states $\propto e^{-\beta E/2}$ of a potential $E$ on a common grid, at inverse temperatures $\beta$ and $\beta+\delta$ with $\delta>0$. With $\Delta=\max E-\min E$,
--   $$|\langle\psi_{\beta+\delta}|\psi_\beta\rangle|\ \ge\ \frac{1}{\cosh(\delta\Delta/4)} .$$
--
--   Consecutive states of a fine temperature schedule overlap, which lets each filtered state warm-start the next.
--
--   Differences from the source:
--   - generalization: a potential $E$ on a common grid → any function $E$ on any finite nonempty set $G$, with $\Delta$ its range on $G$; reason: the grid is one finite set; the proof uses no other structure
-- source:
--   Olivucci, Sobchuk, Hoque, Hnybida, Kim, Shayeghi, Ronagh, Provable Quantum–Classical Separation for Continuous Gibbs Sampling, arXiv:2608.24527 (held version, sha256 d4fd40eb…), Lemma A.8, Eq. (A80), p.31

import Mathlib
import Definitions.Def_GevreyGibbsSep_finiteGibbsState

open MeasureTheory
open scoped ENNReal InnerProductSpace

namespace GevreyGibbsSep

/-- Lemma A.8 (overlap of adjacent Gibbs states), arXiv:2608.24527 (sha256 d4fd40eb…), Eq. (A80),
p.31. For the normalized grid Gibbs states `ψ_β ∝ e^{−βE/2}` of a potential `E` on a common grid,
at inverse temperatures `β` and `β + δ`, `δ > 0`, with `∆ = max E − min E`:
`|⟨ψ_{β+δ}, ψ_β⟩| ≥ 1/cosh(δ∆/4)`.

**Formalization Note** The grid is any finite nonempty set `G` and `E : G → ℝ` any function; the
grid of the paper is one instance, and `∆` is the range of `E` on the grid. -/
theorem lemma_A_8 {G : Type*} [Fintype G] [Nonempty G] (E : G → ℝ) (β δ : ℝ) (hδ : 0 < δ) :
    1 / Real.cosh (δ * (Finset.univ.sup' Finset.univ_nonempty E
        - Finset.univ.inf' Finset.univ_nonempty E) / 4)
      ≤ ‖⟪finiteGibbsState E (β + δ), finiteGibbsState E β⟫_ℂ‖ := by sorry

end GevreyGibbsSep
