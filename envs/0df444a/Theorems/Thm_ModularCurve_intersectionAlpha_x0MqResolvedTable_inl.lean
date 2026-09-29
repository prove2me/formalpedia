-- Prove2me | Theorems.Thm_ModularCurve_intersectionAlpha_x0MqResolvedTable_inl
-- name    : ModularCurve.intersectionAlpha_x0MqResolvedTable_inl
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.700479+00:00
-- url     : https://prove2.me/theorems/4563c54d-44f1-5f2c-97bd-206f20c161af
-- title:
--   Strict-transform rows of the resolved X₀(Mq) intersection table
-- statement:
--   Let `node` be a finite type with decidable equality and let $\mathrm{width} : \mathrm{node} \to \mathbb{N}$ satisfy $1 \le \mathrm{width}\,x$ for every $x$. The component index set is `X0MqComponents width` $= \mathrm{Fin}\,2 \oplus \bigl(\Sigma_{x}\ \mathrm{Fin}(\mathrm{width}\,x - 1)\bigr)$: two distinguished components $\mathrm{inl}\,0,\mathrm{inl}\,1$ together with, for each $x$, a chain of $\mathrm{width}\,x - 1$ further components. The table `x0MqResolvedTable width` has all multiplicities equal to $1$ and intersection numbers $\mathrm{inter}\,i\,j = \mathrm{x0MqAdj}\,i\,j - \delta_{ij}\sum_{j'}\mathrm{x0MqAdj}\,i\,j'$, where `x0MqAdj` is the symmetric $\mathbb{N}$-valued adjacency function on components; and $\mathrm{intersectionAlpha}\,t\,c\,j = \sum_i c\,i \cdot \mathrm{inter}\,i\,j$. Finally `DRResolvedModelPackage.chainPos width n d` is $\mathrm{inl}\,0$ for $d = 0$, is $\mathrm{inr}\,\langle n, d-1\rangle$ for $0 < d < \mathrm{width}\,n$, and is $\mathrm{inl}\,1$ for $d \ge \mathrm{width}\,n$. The assertion is that for every $c : \mathrm{X0MqComponents}\,\mathrm{width} \to \mathbb{Z}$ and every $b \in \mathrm{Fin}\,2$, $$\mathrm{intersectionAlpha}\,(\mathrm{x0MqResolvedTable}\,\mathrm{width})\,c\,(\mathrm{inl}\,b) = \sum_{x}\, c\bigl(\mathrm{chainPos}\,\mathrm{width}\,x\,(\text{$1$ if $b = 0$, else } \mathrm{width}\,x - 1)\bigr) - \#\mathrm{node}\cdot c(\mathrm{inl}\,b).$$
--
--   This computes the rows of the intersection matrix indexed by the two strict transforms in the minimally resolved two-branch special fibre (the fibre at $q$ of $X_0(Mq)$, resp. of the Deligne–Rapoport model of $X_0(p)$ at $p$, after resolving the crossings): each strict transform meets, over every crossing $x$, exactly one further component once — the neighbour at chain position $1$ on one side and at position $\mathrm{width}\,x - 1$ on the other — and has self-intersection $-\#\mathrm{node}$. It is used in the Euler-characteristic computation for sections of the pullback of a strict transform along a surjection of multidegree zero.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_intersectionAlpha_x0MqResolvedTable_inl.lean

import Mathlib
import Definitions.Def_ModularCurve_X0MqResolvedTable
import Definitions.Def_ModularCurve_DRResolvedModelPackageV4

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MazurRapoportAppendix ModularCurve

theorem ModularCurve.intersectionAlpha_x0MqResolvedTable_inl
    {node : Type} [Fintype node] [DecidableEq node] (width : node → ℕ) (hw : ∀ x, 1 ≤ width x)
    (c : X0MqComponents width → ℤ) (b : Fin 2) :
    intersectionAlpha (x0MqResolvedTable width) c (Sum.inl b) =
      (∑ x, c (DRResolvedModelPackage.chainPos width x (if b = 0 then 1 else width x - 1))) -
        (Fintype.card node : ℤ) * c (Sum.inl b) := by sorry
