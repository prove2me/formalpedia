-- Prove2me | Theorems.Thm_NoHair_carter_robinson_axisymmetric_vacuum
-- name    : NoHair.carter_robinson_axisymmetric_vacuum
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-05T00:16:13.171389+00:00
-- url     : https://prove2.me/theorems/c1ba0257-5234-44a8-b70e-6fa6d1e74348
-- title:
--   Carter (1971) / Robinson: axisymmetric vacuum black holes are Kerr
-- statement:
--   Let $(M,g,F,T)$ be a 4-dimensional spacetime: a smooth manifold $M$, a smooth Lorentzian metric $g$ of signature $(-,+,+,+)$, a smooth electromagnetic 2-form $F$ and a time orientation $T$. Assume $(g,F)$ solves the Einstein–Maxwell equations with zero cosmological constant, is stationary under a smooth one-parameter group $\varphi_t$ of isometries preserving $F$, and has a stationary asymptotically flat end $M_{\rm ext}$ on which $\varphi_t$ acts by time translation. Assume the domain of outer communications $\langle\langle M_{\rm ext}\rangle\rangle=I^+(M_{\rm ext})\cap I^-(M_{\rm ext})$ is globally hyperbolic, the black-hole region $M\setminus I^-(M_{\rm ext})$ is nonempty, and the future event horizon $\partial I^-(M_{\rm ext})$ is connected.
--   Assume moreover that $F\equiv0$ (vacuum) and that there is an axial symmetry: a $2\pi$-periodic one-parameter group $\rho_s$ of isometries commuting with $\varphi_t$, with a nonempty axis (common fixed points) and not the identity. Then there are $m>0$ and $a$ with $a^2\le m^2$ such that $\langle\langle M_{\rm ext}\rangle\rangle$ is isometric to the Kerr domain of outer communications with mass $m$ and rotation parameter $a$.
--
--   Carter showed such black holes have only two degrees of freedom; this is the uniqueness statement for spinning vacuum black holes.
-- source:
--   Wikipedia, "No-hair theorem" (revision oldid=1353599195), https://en.wikipedia.org/w/index.php?title=No-hair_theorem&oldid=1353599195

import Mathlib
import Definitions.Def_NoHair_kerrNewman

open scoped ContDiff Manifold BigOperators
open Set Matrix

namespace NoHair

/-- **Milestone (Carter 1971, Robinson 1975): axisymmetric vacuum black holes are Kerr.** -/
theorem carter_robinson_axisymmetric_vacuum {M : Type*} [TopologicalSpace M]
    [ChartedSpace E4 M] [IsManifold 𝓘(ℝ, E4) ∞ M] (g F : BilinField M) (T : VecField M)
    (φ : ℝ → M → M) (E : AsymptoticallyFlatEnd g F φ) (h : IsStationaryBlackHole g F T φ E)
    (hvac : ∀ x, F x = 0) (ρ : ℝ → M → M) (hρ : IsAxialSymmetry g F φ ρ) :
    ∃ m a : ℝ, IsKerrNewmanBlackHoleParams m a 0 ∧
      IsKerrNewmanDOC g F (domainOfOuterCommunications g T E.region) m a 0 := by
  sorry

end NoHair
