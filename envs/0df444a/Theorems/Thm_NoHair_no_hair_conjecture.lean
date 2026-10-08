-- Prove2me | Theorems.Thm_NoHair_no_hair_conjecture
-- name    : NoHair.no_hair_conjecture
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-05T02:34:27.20399+00:00
-- url     : https://prove2.me/theorems/34a3c49b-2381-4caf-8acc-be52e7241ef2
-- title:
--   No-hair conjecture: stationary electrovacuum black holes are Kerr–Newman
-- statement:
--   Let $(M,g,F,T)$ be a 4-dimensional spacetime: a smooth manifold $M$, a smooth Lorentzian metric $g$ of signature $(-,+,+,+)$, a smooth electromagnetic 2-form $F$ and a time orientation $T$. Assume $(g,F)$ solves the Einstein–Maxwell equations with zero cosmological constant, is stationary under a smooth one-parameter group $\varphi_t$ of isometries preserving $F$, and has a stationary asymptotically flat end $M_{\rm ext}$ on which $\varphi_t$ acts by time translation. Assume the domain of outer communications $\langle\langle M_{\rm ext}\rangle\rangle=I^+(M_{\rm ext})\cap I^-(M_{\rm ext})$ is globally hyperbolic, the black-hole region $M\setminus I^-(M_{\rm ext})$ is nonempty, and the future event horizon $\partial I^-(M_{\rm ext})$ is connected.
--
--   Then there are parameters $m>0$, $a$, $e$ with $a^2+e^2\le m^2$ such that $\langle\langle M_{\rm ext}\rangle\rangle$ is isometric to the domain of outer communications $\{r>r_+\}$ of the Kerr–Newman spacetime with mass $m$, angular-momentum parameter $a$ and charge $e$:
--   $$\exists\,\Psi:\{r>r_+\}\xrightarrow{\ \cong\ }\langle\langle M_{\rm ext}\rangle\rangle,\qquad \Psi^*g=g^{KN}_{m,a,e},\qquad \Psi^*F=\cos\beta\,F^{KN}_{a,e}+\sin\beta\,\star F^{KN}_{a,e}$$
--   for some constant duality angle $\beta$.
--
--   This is the precise form of the statement that a stationary black hole of the Einstein–Maxwell theory is characterized by its mass, angular momentum and electric charge. The source states it is unproved in general and is called the no-hair conjecture by mathematicians.
--
--   **Formalization Note** The duality angle $\beta$ allows a magnetic charge, which the source mentions as a possible fourth parameter: the metric depends only on $q^2+p^2=e^2$. Connectedness of the horizon excludes the static multi-black-hole Majumdar–Papapetrou solutions; global hyperbolicity of the domain of outer communications is the standard regularity assumption.
-- source:
--   Wikipedia, "No-hair theorem" (revision oldid=1353599195), https://en.wikipedia.org/w/index.php?title=No-hair_theorem&oldid=1353599195

import Mathlib
import Definitions.Def_NoHair_kerrNewman

open scoped ContDiff Manifold BigOperators
open Set Matrix

namespace NoHair

/-- **Goal (no-hair conjecture, Einstein–Maxwell, Λ = 0).** The domain of outer communications
of every stationary, asymptotically flat electrovacuum black-hole spacetime with globally
hyperbolic domain of outer communications and connected event horizon is isometric to a
Kerr–Newman domain of outer communications (field up to duality rotation). -/
theorem no_hair_conjecture {M : Type*} [TopologicalSpace M] [ChartedSpace E4 M]
    [IsManifold 𝓘(ℝ, E4) ∞ M] (g F : BilinField M) (T : VecField M) (φ : ℝ → M → M)
    (E : AsymptoticallyFlatEnd g F φ) (h : IsStationaryBlackHole g F T φ E) :
    ∃ m a e : ℝ, IsKerrNewmanBlackHoleParams m a e ∧
      IsKerrNewmanDOC g F (domainOfOuterCommunications g T E.region) m a e := by
  sorry

end NoHair
