-- Prove2me | Theorems.Thm_ModularCurve_tateBase_map_coeffMap
-- name    : ModularCurve.tateBase_map_coeffMap
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:54.908972+00:00
-- url     : https://prove2.me/theorems/8a1fc2d1-21b7-57f9-afaa-76079a99e934
-- title:
--   Coefficientwise ring maps carry Tate(q^N) to Tate(q^N)
-- statement:
--   Let $K$ and $K'$ be commutative rings, let $f : K \to K'$ be a ring homomorphism, and let $N$ be a natural number that is nonzero. Write $\mathrm{coeffMap}\,f : K((q)) \to K'((q))$ for the ring homomorphism of Laurent series (Hahn series over $\mathbb{Z}$) obtained by applying $f$ to each coefficient, as given by [`ModularCurve.coeffMap`](def/ModularCurve_LaurentCoeff.html#L16). Write $\mathrm{tateBase}\,K\,N$ for the Weierstrass curve over $K((q))$ obtained from the fixed Weierstrass curve `tatePowerSeries` over $\mathbb{Z}[[q]]$ by pushing its coefficients along `laurentOfInt` into $K((q))$ and then along the substitution $q \mapsto q^N$, i.e. the ring homomorphism `qExpand` induced on Hahn series by multiplication of the exponent group $\mathbb{Z}$ by $N$. The assertion is that applying $\mathrm{coeffMap}\,f$ to each of the five coefficients $a_1, a_2, a_3, a_4, a_6$ of $\mathrm{tateBase}\,K\,N$ yields exactly $\mathrm{tateBase}\,K'\,N$, the corresponding curve over $K'((q))$; that is, $(\mathrm{tateBase}\,K\,N).\mathrm{map}(\mathrm{coeffMap}\,f) = \mathrm{tateBase}\,K'\,N$ as Weierstrass curves over $K'((q))$.
--
--   This records that the Tate curve with parameter $q^N$ is defined over $\mathbb{Z}$, so that its Weierstrass model is insensitive to the coefficient ring: any coefficientwise ring map between Laurent series rings transports it to the corresponding model. It is used when a Tate representative of a point on a modular curve is moved from one coefficient field to another, in the identifications of $j$-invariants at Tate points at full level.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_tateBase_map_coeffMap.lean

import Mathlib
import Definitions.Def_ModularCurve_TateFormal
import Definitions.Def_ModularCurve_TateSlots
import Definitions.Def_ModularCurve_LaurentCoeff

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ModularCurve.tateBase_map_coeffMap {K K' : Type*} [CommRing K] [CommRing K'] (f : K →+* K') (N : ℕ) [NeZero N] :
    (ModularCurve.tateBase K N).map (ModularCurve.coeffMap f) = ModularCurve.tateBase K' N := by sorry
