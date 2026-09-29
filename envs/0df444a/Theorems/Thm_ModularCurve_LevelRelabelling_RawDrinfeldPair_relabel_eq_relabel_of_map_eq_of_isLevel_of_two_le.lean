-- Prove2me | Theorems.Thm_ModularCurve_LevelRelabelling_RawDrinfeldPair_relabel_eq_relabel_of_map_eq_of_isLevel_of_two_le
-- name    : ModularCurve.LevelRelabelling.RawDrinfeldPair.relabel_eq_relabel_of_map_eq_of_isLevel_of_two_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:42.499921+00:00
-- url     : https://prove2.me/theorems/a856d96a-5341-5a37-9646-477fb3cd23ae
-- title:
--   Relabelling a Drinfeld basis depends only on g mod q
-- statement:
--   Let $A$ be a commutative ring, $\mathcal G$ a family of relative group laws assigning to every commutative $A$-algebra $T$, every projective Weierstrass curve $W$ over $T$ and every proof that $\Delta_W$ is a unit a `RelativeGroupLaw` on the projective model structure morphism of $W$; let $q$ be a natural number with $2 \le q$, let $T$ be a commutative $A$-algebra, $W$ a projective Weierstrass curve over $T$, and let $x = (x.\mathrm{curve}, x.P, x.Q)$ be a raw Drinfeld pair over $T$, i.e. a projective Weierstrass curve together with two sections of its projective model over the identity, with $hΔ$ a proof that $x.\mathrm{curve}$ has unit discriminant. Assume `RawDrinfeldPair.IsLevel 𝒢 q W x`, that is: $x.\mathrm{curve} = W$ and, for some proof that $\Delta_{x.\mathrm{curve}}$ is a unit, the pair $(x.P, x.Q)$ satisfies `IsDrinfeldBasis` for the group law $\mathcal G\,T\,x.\mathrm{curve}$ at level $q$, i.e. the basis divisor of $(x.P,x.Q)$ of level $q$ equals the $q$-torsion ideal. Let $g, g'$ be $2 \times 2$ integer matrices whose entrywise images in $\mathrm{M}_2(\mathbb Z/q)$ agree. Then the relabelled pairs coincide: the raw Drinfeld pairs with the same curve and with sections $(g_{00}\cdot x.P + g_{10}\cdot x.Q,\ g_{01}\cdot x.P + g_{11}\cdot x.Q)$ formed via $\mathcal G\,T\,x.\mathrm{curve}\,hΔ$ are equal for $g$ and for $g'$.
--
--   This is the well-definedness of the right action of $\mathrm{GL}_2(\mathbb Z/q)$ on Drinfeld $\Gamma(q)$-level structures at the level of raw pairs: integral relabelling matrices act through their reduction mod $q$, because the members of a Drinfeld basis of level $q$ are killed by $q$. It is used in the study of how relabelling interacts with the moduli parametrisation, in particular by the statements about the action of $\Gamma_0$-type and $H_1$-type matrix powers on the origin parameter, and by the statement that relabelling by $g$ and by a matrix inverse to it mod $q$ returns the original pair.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_LevelRelabelling_RawDrinfeldPair_relabel_eq_relabel_of_map_eq_of_isLevel_of_two_le.lean

import Mathlib
import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_DrinfeldLevelFunctor
import Definitions.Def_ModularCurve_LevelRelabelling

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal

theorem ModularCurve.LevelRelabelling.RawDrinfeldPair.relabel_eq_relabel_of_map_eq_of_isLevel_of_two_le
    {A : Type} [CommRing A] (𝒢 : GroupLaws A) (q : ℕ) (hq : 2 ≤ q)
    (T : Type) [CommRing T] [Algebra A T]
    (W : WeierstrassCurve.Projective T) (x : RawDrinfeldPair T) (hΔ : IsUnit x.curve.Δ)
    (hx : RawDrinfeldPair.IsLevel 𝒢 q W x)
    (g g' : Matrix (Fin 2) (Fin 2) ℤ) (hgg' : g.map (Int.castRingHom (ZMod q)) = g'.map (Int.castRingHom (ZMod q))) :
    ModularCurve.LevelRelabelling.RawDrinfeldPair.relabel 𝒢 g x hΔ =
      ModularCurve.LevelRelabelling.RawDrinfeldPair.relabel 𝒢 g' x hΔ := by sorry
