-- Prove2me | Theorems.Thm_ModularCurve_ord_charLGeomPlaceOfPoint_jqModC_sub_algebraMap
-- name    : ModularCurve.ord_charLGeomPlaceOfPoint_jqModC_sub_algebraMap
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.985053+00:00
-- url     : https://prove2.me/theorems/be37b607-8189-52ac-9952-16e9ec458f2a
-- title:
--   Order of jmath̃-c at the place jmath̃=a
-- statement:
--   Let $k$ be a field and let $a,c\in k$. Write $\tilde\jmath=$ `jqModC k` for the Laurent series over $k$ obtained as $q^{-1}$ times the image of the integral power series `jNum` $=E_4^3\cdot$`dedekindEtaUnitInv` under $\mathbb{Z}\to k$, and let `modularFunctionFieldC k 1` be the intermediate field $k\bigl(\tilde\jmath,\;$`jqNModC k 1`$\bigr)$ of $k(\!(q)\!)$ generated over $k$ by $\tilde\jmath$ together with its level-$1$ $q$-expansion rescaling. The place `charLGeomPlaceOfPoint k a` of this field over $k$ — a valuation subring, distinct from the whole field, containing $k$ and a principal ideal ring — is the transport along the $k$-isomorphism `ratFuncEquivCharLOneC k` $:k(t)\xrightarrow{\sim}$ `modularFunctionFieldC k 1` of the finite place of the rational function field $k(t)$ attached to the irreducible polynomial $X-a$. The assertion is that the associated order function, namely minus the logarithm of the height-one-spectrum valuation, evaluated at the element $\tilde\jmath-c$ of `modularFunctionFieldC k 1` (the series $\tilde\jmath$, which lies in the field by `jqModC_mem`, minus the image of $c$ under the structure map), equals $1$ if $c=a$ and $0$ otherwise.
--
--   This is the elementary local computation at the moduli coordinate: the level-one modular function field is a rational function field in $\tilde\jmath$, and $\tilde\jmath-c$ is a uniformiser exactly at the point $\tilde\jmath=a$ with $a=c$. It serves as the node-coordinate input for the places and stalk computations on the models of modular curves, and is cited by the lemmas on node residues and integrality in the Deligne–Rapoport model package.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_ord_charLGeomPlaceOfPoint_jqModC_sub_algebraMap.lean

import Definitions.Def_ModularCurve_SpecializeModuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve ModularCurve

theorem ModularCurve.ord_charLGeomPlaceOfPoint_jqModC_sub_algebraMap
    (k : Type*) [Field k] [DecidableEq k] (a c : k) :
    (charLGeomPlaceOfPoint k a).ord
        ((⟨jqModC k, jqModC_mem k 1⟩ : ↥(modularFunctionFieldC k 1))
          - algebraMap k ↥(modularFunctionFieldC k 1) c)
      = if c = a then 1 else 0 := by sorry
