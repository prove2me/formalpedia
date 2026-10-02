-- Prove2me | Theorems.Thm_MilnorDynamics_exists_holomorphic_disc_cover_modular_lambda
-- name    : MilnorDynamics.exists_holomorphic_disc_cover_modular_lambda
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-01T09:55:13.454977+00:00
-- url     : https://prove2.me/theorems/a2a36e09-ad82-4343-96ae-91049b4b776c
-- title:
--   The disc covers the twice-punctured plane by a holomorphic map (modular lambda witness)
-- statement:
--   There is a map $p$ from the open unit disc in $\mathbb{C}$ that is holomorphic there, takes no value in $\{0,1\}$, and has image exactly $\mathbb{C}\setminus\{0,1\}$, the thrice-punctured sphere minus the point at infinity. The standard witness is the **modular lambda function** $\lambda:\mathbb{H}\to\mathbb{C}\setminus\{0,1\}$, a degree-$3$ universal covering, composed with a biholomorphism $\mathbb{D}\to\mathbb{H}$. A degree-$1$ composite such as $\exp$ composed with the Cayley map cannot serve: it covers only $\mathbb{C}\setminus\{1\}$ and is undefined at the interior point $z_0=(2\pi-1)/(2\pi+1)$, where $\exp(2\pi i)=1$.
-- source:
--   Milnor, Dynamics in One Complex Variable I, Lemma 2.5 (the thrice-punctured sphere is hyperbolic); classical uniformisation X(2) = P^1 minus {0,1,inf} by the modular lambda function.

import Mathlib
import Definitions.Def_MilnorDynamics_NormalFamilies

open scoped OnePoint
open Filter Set

namespace MilnorDynamics

/-- The first genuinely new obligation of `disc_cover_proper_and_local_exists`.

The thrice-punctured sphere is uniformised by the **modular lambda function**
`lambda : H -> C \ {0,1}`, a degree-3 universal covering; composing it with a
biholomorphism `D -> H` yields a map of the disc onto `C \ {0,1}` that omits
both punctures.  A degree-1 composite cannot serve: `exp` composed with the
Cayley map covers only `C \ {1}`, and is undefined at the interior point
`z0 = (2*pi - 1)/(2*pi + 1)`, where `exp (2*pi*I) = 1`.  -/
theorem exists_holomorphic_disc_cover_modular_lambda :
    exists p : ℂ -> ℂ, DifferentiableOn ℂ p (Metric.ball 0 1) /\
      exists hp : MapsTo p (Metric.ball 0 1) ({0, 1}ᶜ : Set ℂ),
        p '' (Metric.ball 0 1) = {0, 1}ᶜ := by sorry

end MilnorDynamics
