-- Prove2me | Theorems.Thm_GibbsTransition_SizeCopies_small_volume_ground_states
-- name    : GibbsTransition.SizeCopies.small_volume_ground_states
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T21:52:47.942174+00:00
-- url     : https://prove2.me/theorems/e390e666-9ebe-4954-9f04-cafe7082b0ef
-- title:
--   Lemma 4.2 — Ground states at small system sizes
-- statement:
--   Let $r$ be algebraic with $0\le r\le1/4$, let $L\ge1$, and suppose $rL<6\kappa$. For the ferromagnet (18), write $\omega_{s,L}$ for the pure uniform-$s$ projector. At every real field $\phi\in[0,1]$, its complete normalized ground density is
--
--   $$\rho^\infty_{r,L}(\phi)=\begin{cases}\omega_{A,L},&\phi<1/2,\\(\omega_{A,L}+\omega_{B,L})/2,&\phi=1/2,\\\omega_{B,L},&\phi>1/2.\end{cases}$$
--
--   The interaction belongs to $\mathcal C^*$ and its transition target is $\theta_r=1/2-r$.
--
--   This identifies the full finite-system states, including degeneracy, while retaining the different infinite-volume transition. Algebraicity is the standing local-entry convention of §2.1, required for the membership clause.
--
--   Differences from the source:
--   - encoding: normalized entire ground-space projector and uniform basis projectors → finite spectral functional calculus and configuration-indexed matrices; reason: the spectral indicator includes every least eigenvector, including at φ=1/2
-- source:
--   Yuhao Cai, Zhenzhang Li, STOC 2027 submission #1168 (October 2026), Lemma 4.2, Equation (19), printed p. 7 (PDF p. 9); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1168.pdf

import Mathlib
import Definitions.Def_GibbsTransition_SizeCopies_Physics

namespace GibbsTransition.SizeCopies

/-- Lemma 4.2, printed p.7 (PDF p.9). Algebraicity is the inherited
local-interaction convention of §2.1. The full ground projector is normalized. -/
theorem small_volume_ground_states (r : ℝ) (hrAlg : IsAlgebraic ℚ r)
    (hr0 : 0 ≤ r) (hr1 : r ≤ 1/4) (L : ℕ) (hL : 1 ≤ L)
    (hrL : r * (L : ℝ) < 6*kappa) :
    InClass (ferromagnet r) ∧ transitionPoint (ferromagnet r) = 1/2-r ∧
      ∀ phi ∈ Set.Icc (0 : ℝ) 1,
        groundDensity (ferromagnet r) L phi =
          if phi < 1/2 then uniformProjector L 0 else
            if phi = 1/2 then (1/2 : ℂ) •
              (uniformProjector L 0 + uniformProjector L 1)
            else uniformProjector L 1 := by sorry

end GibbsTransition.SizeCopies
