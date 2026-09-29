-- Prove2me | Theorems.Thm_MvFormalGroup_Deformation_isShiftBy_add_smul_of_toPowerSeries_eq_add_smul_sub
-- name    : MvFormalGroup.Deformation.isShiftBy_add_smul_of_toPowerSeries_eq_add_smul_sub
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.856965+00:00
-- url     : https://prove2.me/theorems/ebe97730-49e7-57d7-b465-c0ae20d35b96
-- title:
--   Shift classes add under affine combinations of deformations
-- statement:
--   Let $B$ be a local commutative ring with residue map $\mathrm{residue}\colon B \to k$, $k =$ its residue field, let $B_1$ be a commutative $B$-algebra, let $V$ be an abelian group carrying a $k$-module structure and a $B$-module structure compatible with it via the residue map, and let $\iota\colon V \to B$ be $B$-linear. Let $F$ be a $d$-dimensional formal group law over $B$, and let $G_0, G, G', G''$ be deformations of $F \otimes_B B_1$ to $B$, i.e. formal group laws over $B$ whose base change along $B \to B_1$ equals $F.\mathrm{map}(\mathrm{algebraMap}\,B\,B_1)$. Let $w, w'$ be $k$-linear maps from the $k$-dual of $V$ to the first-order deformation space of $F \otimes_B k$ (first-order cocycles modulo coboundaries, as tuples of power series in $\mathrm{Fin}\,d \oplus \mathrm{Fin}\,d$ variables over $k$), let $a \in k$ and let $al \in B$ lift $a$. Assume that coefficientwise, for every $l \in \mathrm{Fin}\,d$, the $l$-th power series of $G''$ equals that of $G$ plus $al$ times the difference of those of $G'$ and $G_0$, and that `Deformation.IsShiftBy` holds for $(w, G_0, G)$ and for $(w', G_0, G')$: that is, there are finite families $v_i \in V$, cocycles $z_i$ and lifts $zl_i$ of $z_i$ to tuples of power series over $B$ with $w(\xi) = \sum_i \xi(v_i)[z_i]$ for all $\xi$ and $G = G_0 + \sum_i \iota(v_i)\,zl_i$ coefficientwise, and likewise for $w'$, $G'$. Then `Deformation.IsShiftBy` holds for $(w + a\,w', G_0, G'')$.
--
--   This is the additivity/linearity property of the shift invariant attached to a pair of deformations: a deformation obtained as the affine combination $G + al\,(G' - G_0)$ of two deformations of $F \otimes_B B_1$ has shift class the corresponding combination $w + a\,w'$ of the two shift classes. It is used in the analysis of deformations of the formal group attached to a Jacobian with good reduction, where the shift classes are compared with tangent coordinates of a pair of lifts.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_MvFormalGroup_Deformation_isShiftBy_add_smul_of_toPowerSeries_eq_add_smul_sub.lean

import Definitions.Def_CerednikDrinfeld_QMFormalModuleOf
import Definitions.Def_MvFormalGroup_IsShiftBy

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsLocalRing MvFormalGroup

theorem MvFormalGroup.Deformation.isShiftBy_add_smul_of_toPowerSeries_eq_add_smul_sub
    {B : Type} [CommRing B] [IsLocalRing B] {B₁ : Type} [CommRing B₁] [Algebra B B₁]
    (V : Type) [AddCommGroup V] [Module (ResidueField B) V] [Module B V] [IsScalarTower B (ResidueField B) V]
    (ι : V →ₗ[B] B) {d : ℕ} (F : MvFormalGroup d B)
    (G₀ G G' G'' : Deformation (F.map (algebraMap B B₁)) B)
    (w w' : Module.Dual (ResidueField B) V →ₗ[ResidueField B] firstOrderDeformationSpace (F.map (residue B)))
    (a : ResidueField B) (al : B) (hal : residue B al = a)
    (hG'' : ∀ l : Fin d, G''.F.toPowerSeries l = G.F.toPowerSeries l + al • (G'.F.toPowerSeries l - G₀.F.toPowerSeries l))
    (h : Deformation.IsShiftBy V ι F w G₀ G) (h' : Deformation.IsShiftBy V ι F w' G₀ G') :
    Deformation.IsShiftBy V ι F (w + a • w') G₀ G'' := by sorry
