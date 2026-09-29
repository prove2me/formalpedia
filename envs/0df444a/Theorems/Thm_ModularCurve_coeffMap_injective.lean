-- Prove2me | Theorems.Thm_ModularCurve_coeffMap_injective
-- name    : ModularCurve.coeffMap_injective
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:49.598281+00:00
-- url     : https://prove2.me/theorems/b5b348dd-46df-59d9-bc45-da150bc74902
-- title:
--   Coefficientwise map on Laurent series preserves injectivity
-- statement:
--   Let $R$ and $S$ be commutative rings and let $f\colon R\to S$ be a ring homomorphism. The project's [`ModularCurve.coeffMap f`](def/ModularCurve_LaurentCoeff.html#L16) is the ring homomorphism $R((q))\to S((q))$ between formal Laurent series rings, realised as Hahn series with value group $\mathbb{Z}$, that applies $f$ to each coefficient: the series $x$ with coefficients $(x_k)_{k\in\mathbb{Z}}$ is sent to the series with coefficients $(f(x_k))_{k\in\mathbb{Z}}$ (its support being contained in that of $x$), and this assignment respects $0$, $1$, addition and multiplication. The assertion is that if $f$ is injective as a function $R\to S$, then [`ModularCurve.coeffMap f`](def/ModularCurve_LaurentCoeff.html#L16) is injective as a function $R((q))\to S((q))$.
--
--   An elementary functoriality statement for the coefficientwise extension of a ring homomorphism to formal Laurent series; it underlies the coefficient embedding $\mathbb{Q}((q))\to L((q))$ used to base change intermediate fields of $\mathbb{Q}((q))/\mathbb{Q}$ to a field $L$ of characteristic zero. It is invoked throughout the treatment of $q$-expansions on modular curves, for instance in the constructions of charts, poles and level fields attached to full-level structures.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_coeffMap_injective.lean

import Definitions.Def_ModularCurve_LaurentCoeff

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ModularCurve.coeffMap_injective {R S : Type*} [CommRing R] [CommRing S] {f : R →+* S} (hf : Function.Injective f) : Function.Injective (ModularCurve.coeffMap f) := by sorry
