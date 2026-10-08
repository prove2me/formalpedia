-- Prove2me | Theorems.Thm_NoHair_israel_static_vacuum
-- name    : NoHair.israel_static_vacuum
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-04T22:25:34.527845+00:00
-- url     : https://prove2.me/theorems/1931bf7b-9b31-4f01-9a4c-3563c9cdbf9a
-- title:
--   Israel (1967): static vacuum black holes are Schwarzschild
-- statement:
--   Let $(M,g,F,T)$ be a 4-dimensional spacetime: a smooth manifold $M$, a smooth Lorentzian metric $g$ of signature $(-,+,+,+)$, a smooth electromagnetic 2-form $F$ and a time orientation $T$. Assume $(g,F)$ solves the Einstein–Maxwell equations with zero cosmological constant, is stationary under a smooth one-parameter group $\varphi_t$ of isometries preserving $F$, and has a stationary asymptotically flat end $M_{\rm ext}$ on which $\varphi_t$ acts by time translation. Assume the domain of outer communications $\langle\langle M_{\rm ext}\rangle\rangle=I^+(M_{\rm ext})\cap I^-(M_{\rm ext})$ is globally hyperbolic, the black-hole region $M\setminus I^-(M_{\rm ext})$ is nonempty, and the future event horizon $\partial I^-(M_{\rm ext})$ is connected.
--   Assume moreover that $F\equiv0$ (vacuum) and that the stationary Killing field $K$ is hypersurface-orthogonal ($K\wedge dK=0$) on $\langle\langle M_{\rm ext}\rangle\rangle$ (static). Then for some $m>0$, $\langle\langle M_{\rm ext}\rangle\rangle$ is isometric to the Schwarzschild exterior $\{r>2m\}$, i.e. to the Kerr–Newman domain of outer communications with $a=e=0$.
--
--   This is the first uniqueness theorem in the history of the problem.
-- source:
--   Wikipedia, "No-hair theorem" (revision oldid=1353599195), https://en.wikipedia.org/w/index.php?title=No-hair_theorem&oldid=1353599195

import Mathlib
import Definitions.Def_NoHair_kerrNewman

open scoped ContDiff Manifold BigOperators
open Set Matrix

namespace NoHair

/-- **Milestone (Israel 1967): static vacuum black holes are Schwarzschild.** -/
theorem israel_static_vacuum {M : Type*} [TopologicalSpace M] [ChartedSpace E4 M]
    [IsManifold 𝓘(ℝ, E4) ∞ M] (g F : BilinField M) (T : VecField M) (φ : ℝ → M → M)
    (E : AsymptoticallyFlatEnd g F φ) (h : IsStationaryBlackHole g F T φ E)
    (hvac : ∀ x, F x = 0)
    (hstatic : IsStaticOn g φ (domainOfOuterCommunications g T E.region)) :
    ∃ m : ℝ, 0 < m ∧
      IsKerrNewmanDOC g F (domainOfOuterCommunications g T E.region) m 0 0 := by
  sorry

end NoHair
