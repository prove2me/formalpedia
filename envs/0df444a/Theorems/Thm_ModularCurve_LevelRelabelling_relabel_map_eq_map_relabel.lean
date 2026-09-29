-- Prove2me | Theorems.Thm_ModularCurve_LevelRelabelling_relabel_map_eq_map_relabel
-- name    : ModularCurve.LevelRelabelling.relabel_map_eq_map_relabel
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:42.499921+00:00
-- url     : https://prove2.me/theorems/f11a6027-ec49-5dbe-b68a-15e814ec1de5
-- title:
--   Relabelling of level data commutes with base change
-- statement:
--   Let $T$ and $T'$ be fields in a common universe, $f\colon T \to T'$ a ring homomorphism, $W$ a Weierstrass curve over $T$, $g$ a $2\times 2$ matrix with integer entries, and $D$ a [`ModularCurve.LevelPData`](def/ModularCurve_KatzLevelP.html#L43) over $T$, that is a quadruple of elements $x_P, y_P, x_Q, y_Q$ of $T$. Write $D.\mathrm{map}\,f$ for the quadruple obtained by applying $f$ to each of the four coordinates, and $W.\mathrm{map}\,f$ for the base-changed Weierstrass curve. The relabelling operation `LevelPData.relabel` attached to a curve over a field proceeds as follows: it converts $(x_P,y_P)$ and $(x_Q,y_Q)$ into points $P$, $Q$ of the affine Mordell–Weil group `W.toAffine.Point` by `toPoint`, which returns the affine point with these coordinates when the pair is nonsingular on the affine model and the point at infinity otherwise; it forms $g_{00}\cdot P + g_{10}\cdot Q$ and $g_{01}\cdot P + g_{11}\cdot Q$ in that group; and it reads the coordinates back off by `ofPoint`, which returns $(x,y)$ for an affine point and the pair $(0,0)$ for the point at infinity. The assertion is that relabelling by $g$ the base-changed data $D.\mathrm{map}\,f$ on $W.\mathrm{map}\,f$ gives exactly the result of relabelling $D$ by $g$ on $W$ and then applying $f$ to the four coordinates.
--
--   This is the functoriality in the base of the right action of integral $2\times 2$ matrices on coordinate-level level-$p$ data, in the row-vector convention $(P,Q)\mapsto (P,Q)g$. It is used wherever relabelled level structures must be compared after extension of the base field, for instance in the determinant and level-automorphism statements of the full-level constructions that cite it.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_LevelRelabelling_relabel_map_eq_map_relabel.lean

import Mathlib
import Definitions.Def_ModularCurve_KatzLevelP
import Definitions.Def_ModularCurve_LevelRelabelling

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open ModularCurve ModularCurve.LevelRelabelling
open scoped Classical

theorem ModularCurve.LevelRelabelling.relabel_map_eq_map_relabel
    {T T' : Type u} [Field T] [Field T'] (f : T →+* T')
    (W : WeierstrassCurve T) (g : Matrix (Fin 2) (Fin 2) ℤ) (D : ModularCurve.LevelPData T) :
    LevelPData.relabel (W.map f) g (D.map f) = (LevelPData.relabel W g D).map f := by sorry
