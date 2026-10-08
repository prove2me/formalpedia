-- Prove2me | Theorems.Thm_NoHair_hawking_analytic_nondegenerate_vacuum
-- name    : NoHair.hawking_analytic_nondegenerate_vacuum
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-05T00:40:50.439978+00:00
-- url     : https://prove2.me/theorems/d3c7be7a-309a-40fd-b177-28ba5a1b316c
-- title:
--   Hawking–Carter–Robinson: analytic non-degenerate vacuum black holes are Kerr
-- statement:
--   Let $(M,g,F,T)$ be a 4-dimensional spacetime: a smooth manifold $M$, a smooth Lorentzian metric $g$ of signature $(-,+,+,+)$, a smooth electromagnetic 2-form $F$ and a time orientation $T$. Assume $(g,F)$ solves the Einstein–Maxwell equations with zero cosmological constant, is stationary under a smooth one-parameter group $\varphi_t$ of isometries preserving $F$, and has a stationary asymptotically flat end $M_{\rm ext}$ on which $\varphi_t$ acts by time translation. Assume the domain of outer communications $\langle\langle M_{\rm ext}\rangle\rangle=I^+(M_{\rm ext})\cap I^-(M_{\rm ext})$ is globally hyperbolic, the black-hole region $M\setminus I^-(M_{\rm ext})$ is nonempty, and the future event horizon $\partial I^-(M_{\rm ext})$ is connected.
--   Assume moreover that $F\equiv0$ (vacuum), that $M$ is a real-analytic manifold and $g$ has real-analytic components in every chart, and that the event horizon $H$ is non-degenerate: there are a Killing field $X$ generating a one-parameter group of isometries and a constant $\kappa\neq0$ such that on $H\cap\overline{\langle\langle M_{\rm ext}\rangle\rangle}$, $X$ is null, not identically zero, and $\nabla(g(X,X))=-2\kappa X^\flat$. Then $\langle\langle M_{\rm ext}\rangle\rangle$ is isometric to a Kerr domain of outer communications $(m,a)$, $m>0$, $a^2\le m^2$.
--
--   This is the partially resolved case of the conjecture described in the source.
--
--   **Formalization Note** Non-degeneracy is expressed through a Killing horizon with nonzero surface gravity $\kappa$.
-- source:
--   Wikipedia, "No-hair theorem" (revision oldid=1353599195), https://en.wikipedia.org/w/index.php?title=No-hair_theorem&oldid=1353599195

import Mathlib
import Definitions.Def_NoHair_kerrNewman

open scoped ContDiff Manifold BigOperators
open Set Matrix

namespace NoHair

/-- **Milestone (Hawking–Carter–Robinson): analytic vacuum black holes with non-degenerate
horizon are Kerr.** -/
theorem hawking_analytic_nondegenerate_vacuum {M : Type*} [TopologicalSpace M]
    [ChartedSpace E4 M] [IsManifold 𝓘(ℝ, E4) ∞ M] [IsManifold 𝓘(ℝ, E4) ω M]
    (g F : BilinField M) (T : VecField M)
    (φ : ℝ → M → M) (E : AsymptoticallyFlatEnd g F φ) (h : IsStationaryBlackHole g F T φ E)
    (hvac : ∀ x, F x = 0) (hanalytic : IsAnalyticBilinField g)
    (hnondeg : IsNondegenerateHorizon g F (futureEventHorizon g T E.region)
      (domainOfOuterCommunications g T E.region)) :
    ∃ m a : ℝ, IsKerrNewmanBlackHoleParams m a 0 ∧
      IsKerrNewmanDOC g F (domainOfOuterCommunications g T E.region) m a 0 := by
  sorry

end NoHair
