-- Prove2me | Theorems.Thm_ModularCurve_map_coeffMap_tateLaurent
-- name    : ModularCurve.map_coeffMap_tateLaurent
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.34379+00:00
-- url     : https://prove2.me/theorems/8b2bc90c-ba90-5d2f-8aa2-d969fa471f45
-- title:
--   Base change of the Tate curve along a coefficient map
-- statement:
--   Let $K$ and $K'$ be commutative rings and let $f : K \to K'$ be a ring homomorphism. Write `coeffMap f` for the ring homomorphism $K((q)) \to K'((q))$ on Laurent series (Hahn series over $\mathbb{Z}$ with values in the coefficient ring) obtained by applying $f$ to every coefficient, and write `tateLaurent K` for the Weierstrass curve over $K((q))$ whose coefficients are the images under `laurentOfInt K` of the coefficients $(a_1,a_2,a_3,a_4,a_6) = (1,0,0,\mathrm{tateA4},\mathrm{tateA6})$ of the integral power-series model `tatePowerSeries`; here `laurentOfInt K` is the composite of the coefficientwise map $\mathbb{Z} \to K$ on power series with the inclusion of power series into Laurent series. The theorem asserts that pushing `tateLaurent K` forward along `coeffMap f`, that is applying `coeffMap f` to each of its five coefficients, yields exactly `tateLaurent K'`. There are no further hypotheses: the two rings and the homomorphism $f$ are all that is needed, the content being that reading the fixed integral series $\mathrm{tateA4}$ and $\mathrm{tateA6}$ in $K$ and then applying $f$ coefficientwise agrees with reading them in $K'$ directly.
--
--   This is the statement that the Tate curve over a ring of Laurent series is the base change of a single model with integral coefficients, so that all its coefficients commute with change of the coefficient ring; typical instances are $\mathbb{Z} \hookrightarrow \mathbb{Q}$, reduction modulo a prime, and the action of a field automorphism. It is used to transport identities about the Tate curve and its invariants between coefficient rings, and is cited in the treatment of Katz modular forms of weight two.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_map_coeffMap_tateLaurent.lean

import Definitions.Def_ModularCurve_TateFormal
import Definitions.Def_ModularCurve_LaurentCoeff

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open PowerSeries HahnSeries ModularCurve

theorem ModularCurve.map_coeffMap_tateLaurent (K : Type*) [CommRing K] (K' : Type*) [CommRing K']
    (f : K →+* K') : (tateLaurent K).map (coeffMap f) = tateLaurent K' := by sorry
