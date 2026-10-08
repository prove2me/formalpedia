-- Prove2me | Theorems.Thm_NoHair_israel_static_electrovac
-- name    : NoHair.israel_static_electrovac
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-04T22:55:25.75193+00:00
-- url     : https://prove2.me/theorems/ae80f2c5-e7b6-4f5e-ab99-ed248fa30fca
-- title:
--   Israel (1968): static electrovacuum black holes are Reissner–Nordström
-- statement:
--   Let $(M,g,F,T)$ be a 4-dimensional spacetime: a smooth manifold $M$, a smooth Lorentzian metric $g$ of signature $(-,+,+,+)$, a smooth electromagnetic 2-form $F$ and a time orientation $T$. Assume $(g,F)$ solves the Einstein–Maxwell equations with zero cosmological constant, is stationary under a smooth one-parameter group $\varphi_t$ of isometries preserving $F$, and has a stationary asymptotically flat end $M_{\rm ext}$ on which $\varphi_t$ acts by time translation. Assume the domain of outer communications $\langle\langle M_{\rm ext}\rangle\rangle=I^+(M_{\rm ext})\cap I^-(M_{\rm ext})$ is globally hyperbolic, the black-hole region $M\setminus I^-(M_{\rm ext})$ is nonempty, and the future event horizon $\partial I^-(M_{\rm ext})$ is connected.
--   Assume moreover that the stationary Killing field is hypersurface-orthogonal on $\langle\langle M_{\rm ext}\rangle\rangle$ (static). Then there are $m>0$ and $e$ with $e^2\le m^2$ such that $\langle\langle M_{\rm ext}\rangle\rangle$ is isometric to the Reissner–Nordström exterior with mass $m$ and charge $e$ (the Kerr–Newman domain of outer communications with $a=0$), the field matching up to a constant duality rotation.
--
--   This is the charged generalization of Israel's theorem.
-- source:
--   Wikipedia, "No-hair theorem" (revision oldid=1353599195), https://en.wikipedia.org/w/index.php?title=No-hair_theorem&oldid=1353599195

import Mathlib
import Definitions.Def_NoHair_kerrNewman

open scoped ContDiff Manifold BigOperators
open Set Matrix

namespace NoHair

/-- **Milestone (Israel 1968): static electrovacuum black holes are Reissner–Nordström.** -/
theorem israel_static_electrovac {M : Type*} [TopologicalSpace M] [ChartedSpace E4 M]
    [IsManifold 𝓘(ℝ, E4) ∞ M] (g F : BilinField M) (T : VecField M) (φ : ℝ → M → M)
    (E : AsymptoticallyFlatEnd g F φ) (h : IsStationaryBlackHole g F T φ E)
    (hstatic : IsStaticOn g φ (domainOfOuterCommunications g T E.region)) :
    ∃ m e : ℝ, IsKerrNewmanBlackHoleParams m 0 e ∧
      IsKerrNewmanDOC g F (domainOfOuterCommunications g T E.region) m 0 e := by
  sorry

end NoHair
