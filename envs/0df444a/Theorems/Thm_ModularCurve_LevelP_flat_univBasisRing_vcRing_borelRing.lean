-- Prove2me | Theorems.Thm_ModularCurve_LevelP_flat_univBasisRing_vcRing_borelRing
-- name    : ModularCurve.LevelP.flat_univBasisRing_vcRing_borelRing
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:42.499921+00:00
-- url     : https://prove2.me/theorems/bfcc847c-1a3f-5d7c-8afa-93c0435310bc
-- title:
--   Flatness of the universal level-p basis, coordinate-change and Borel rings
-- statement:
--   For every natural number $p$ the following three flatness assertions hold. First, the universal level-$p$ basis ring $\mathcal T =$ [`ModularCurve.LevelP.UnivBasisRing p`](def/ModularCurve_KatzLevelPUniversal.html#L274), that is `BasisRing (univCurve p) p`, the localisation away from the element `indepDenom (univCurve p) p` of the two-point ring of the curve `univCurve p` (the generic Weierstrass curve over `MvPolynomial (Fin 5) ℤ` base-changed to `UnivBase p`), is flat as a $\mathbb Z$-module. Secondly, [`ModularCurve.LevelP.VCRing p`](def/ModularCurve_KatzLevelPClassifyingMaps.html#L304), the localisation of the four-variable polynomial ring `MvPolynomial (Fin 4) (UnivBasisRing p)` away from the variable `MvPolynomial.X 0`, is flat as a module over $\mathcal T$. Thirdly, for every natural number $a$, the ring [`ModularCurve.LevelP.BorelRing p a`](def/ModularCurve_KatzLevelPClassifyingMaps.html#L480), the localisation of `BorelPRing p a = TorsionPointRing (borelQCurve p a) p` away from the element `borelDenom p a`, the product of the two independence elements `indepElt (borelPCurve p a) p` of the pair of abscissae `BorelPRing.xP p a`, `BorelPRing.xQ p a` taken in both orders, is flat as a module over $\mathcal T$. No primality or positivity hypothesis on $p$ (or on $a$) is imposed.
--
--   The three rings are the base rings of the universal level-$p$ situation, of the universal change of Weierstrass coordinates over it, and of the universal Borel pairs of exponent $a$; their flatness is what allows base change along them to be exact, as in the Katz–Mazur treatment of level structures. It is used in the proofs that a Katz level-$p$ form depending only on the lines (or only on the second line) and vanishing at the cusps vanishes identically, and in the construction of a Katz $\Gamma_0$-form with prescribed value at a cusp.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_LevelP_flat_univBasisRing_vcRing_borelRing.lean

import Mathlib
import Definitions.Def_ModularCurve_KatzLevelP
import Definitions.Def_ModularCurve_KatzLevelPUniversal
import Definitions.Def_ModularCurve_KatzLevelPClassifyingMaps

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ModularCurve.LevelP.flat_univBasisRing_vcRing_borelRing (p : ℕ) :
    Module.Flat ℤ (ModularCurve.LevelP.UnivBasisRing p) ∧
      Module.Flat (ModularCurve.LevelP.UnivBasisRing p) (ModularCurve.LevelP.VCRing p) ∧
        ∀ a : ℕ, Module.Flat (ModularCurve.LevelP.UnivBasisRing p) (ModularCurve.LevelP.BorelRing p a) := by sorry
