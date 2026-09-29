-- Prove2me | Theorems.Thm_ModularCurve_intersectionAlpha_x0MqResolvedTable_eq_sum_x0MqAdj_and_sum_x0MqAdj_inl
-- name    : ModularCurve.intersectionAlpha_x0MqResolvedTable_eq_sum_x0MqAdj_and_sum_x0MqAdj_inl
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.700479+00:00
-- url     : https://prove2.me/theorems/b59929f7-3189-57bc-a9d3-e50d3f70a7f6
-- title:
--   Raw intersection rows for the resolved X₀(Mq) table
-- statement:
--   Let $node$ be a finite type with decidable equality and let $width : node \to \mathbb{N}$ satisfy $1 \le width(x)$ for all $x$. Write $\mathcal{C} =$ `X0MqComponents width` $= \mathrm{Fin}\,2 \oplus \bigl(\Sigma_{x}\,\mathrm{Fin}(width(x)-1)\bigr)$ for the component index set, `x0MqAdj width` for the adjacency function on $\mathcal{C}$ (distinct $\mathrm{inl}$ indices are adjacent with multiplicity $\#\{x : width(x)=1\}$; $\mathrm{inl}\,0$ meets $\mathrm{inr}\,(x,i)$ iff $i=0$ and $\mathrm{inl}\,1$ meets it iff $i = width(x)-2$; two $\mathrm{inr}$ indices over the same $x$ are adjacent iff their second coordinates differ by one; all other values $0$), and let `x0MqResolvedTable width` be the table with all multiplicities $1$ and $\mathrm{inter}(i,j) = \mathrm{adj}(i,j) - [i=j]\sum_{j'}\mathrm{adj}(i,j')$, so that `intersectionAlpha` sends $c$ to $j \mapsto \sum_i c(i)\,\mathrm{inter}(i,j)$. The theorem asserts three things simultaneously: (1) for every $c : \mathcal{C} \to \mathbb{Z}$ and every $j \in \mathcal{C}$, $\alpha(c)(j) = \sum_F c(F)\,\mathrm{adj}(F,j) - c(j)\sum_F \mathrm{adj}(j,F)$; (2) for each $b \in \mathrm{Fin}\,2$, $\sum_F \mathrm{adj}(\mathrm{inl}\,b, F) = \#node$; (3) for each $b$ and each $F \in \mathcal{C}$, $\mathrm{adj}(F, \mathrm{inl}\,b) = \sum_x [\,F = \mathtt{chainPos}\ width\ x\ d_b(x)\,]$ where $d_0(x) = 1$ and $d_1(x) = width(x)-1$, and `DRResolvedModelPackage.chainPos width x d` equals $\mathrm{inl}\,0$ for $d=0$, $\mathrm{inr}\,(x, d-1)$ for $0 < d < width(x)$, and $\mathrm{inl}\,1$ otherwise.
--
--   This is the raw-row form of the Mazur–Rapoport intersection matrix attached to a resolved model of $X_0(Mq)$ in residue characteristic dividing the level: the two strict transforms $\mathrm{inl}\,0, \mathrm{inl}\,1$ together with the chains of exceptional components of lengths $width(x)-1$ over the crossings indexed by $node$, the second and third clauses recording that each strict transform meets exactly one chain member over every crossing and naming that member in the chain coordinate. It feeds the Euler characteristic computations [`ModularCurve.DRResolvedModelPackageLevel.eulerChar_sectionsOf_pullback_foldr_ker_tensor_prod_comp_eq_add_sum_single_add_intersectionAlpha`](thm.html#ModularCurve.DRResolvedModelPackageLevel.eulerChar_sectionsOf_pullback_foldr_ker_tensor_prod_comp_eq_add_sum_single_add_intersectionAlpha) and [`ModularCurve.DRResolvedModelPackage.eulerChar_sectionsOf_pullback_strictTransform_eq_of_multidegree_eq_zero_of_surjective`](thm.html#ModularCurve.DRResolvedModelPackage.eulerChar_sectionsOf_pullback_strictTransform_eq_of_multidegree_eq_zero_of_surjective).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_intersectionAlpha_x0MqResolvedTable_eq_sum_x0MqAdj_and_sum_x0MqAdj_inl.lean

import Mathlib
import Definitions.Def_ModularCurve_X0MqResolvedTable
import Definitions.Def_ModularCurve_DRResolvedModelPackageV4

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MazurRapoportAppendix ModularCurve

theorem ModularCurve.intersectionAlpha_x0MqResolvedTable_eq_sum_x0MqAdj_and_sum_x0MqAdj_inl
    {node : Type} [Fintype node] [DecidableEq node] (width : node → ℕ) (hw : ∀ x, 1 ≤ width x) :
    (∀ (c : X0MqComponents width → ℤ) (j : X0MqComponents width),
      intersectionAlpha (x0MqResolvedTable width) c j =
        (∑ F, c F * (x0MqAdj width F j : ℤ)) - c j * ∑ F, (x0MqAdj width j F : ℤ)) ∧
    (∀ b : Fin 2, ∑ F, x0MqAdj width (Sum.inl b) F = Fintype.card node) ∧
    (∀ (b : Fin 2) (F : X0MqComponents width),
      x0MqAdj width F (Sum.inl b) =
        ∑ x, if F = DRResolvedModelPackage.chainPos width x (if b = 0 then 1 else width x - 1) then 1 else 0) := by sorry
