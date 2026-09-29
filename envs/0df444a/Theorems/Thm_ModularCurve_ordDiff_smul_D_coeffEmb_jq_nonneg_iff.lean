-- Prove2me | Theorems.Thm_ModularCurve_ordDiff_smul_D_coeffEmb_jq_nonneg_iff
-- name    : ModularCurve.ordDiff_smul_D_coeffEmb_jq_nonneg_iff
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.985053+00:00
-- url     : https://prove2.me/theorems/26efb9b3-19cc-51d0-80e9-82f008109973
-- title:
--   Regularity of x dj at a place where ord j ≠ 0
-- statement:
--   Let $K$ be a field equipped with a $\mathbb{Q}$-algebra structure and let $N$ be a nonzero natural number. Write $F =$ `laurentBaseChange K (modularFunctionFieldFull N)`, the intermediate field of $K((q))$ generated over $K$ by the coefficientwise image under `coeffEmb K` (the map on Laurent series induced by $\mathbb{Q} \to K$) of `modularFunctionFieldFull N`, the subfield of $\mathbb{Q}((q))$ generated over $\mathbb{Q}$ by the expansions `qExpand ℚ d jq` for the divisors $d$ of $N$, where `jq` $= q^{-1}\cdot$`jNumQ` is the $q$-expansion of $j$. Let $w$ be a place of $F$ over $K$, i.e. a valuation subring of $F$ containing $K$, distinct from $F$ and a principal ideal ring, with associated order function `w.ord` given by minus the logarithm of its adic valuation. Let $J \in F$ denote the image of `jq` under `coeffEmb K`, and assume $w.\mathrm{ord}(J) \neq 0$. Then for every nonzero $x \in F$, the quantity $w.\mathrm{ordDiff}(x \cdot dJ)$ — the $w$-order of the coefficient of $x \cdot dJ \in \Omega_{F/K}$ with respect to a uniformiser at $w$ — is nonnegative if and only if $w.\mathrm{ord}(x) \geq 1 - w.\mathrm{ord}(J)$.
--
--   This is the local regularity criterion for differentials of the form $x\,dj$ on the modular curve at a place where $j$ has nonzero order, such as a cusp: at a cusp of width $h$ the differential $dj$ has a pole of order $h+1$, so $x\,dj$ is regular precisely when $x$ vanishes to order at least $h+1$. It feeds the identification of regular differentials on $X_0(N)$ with weight two forms, being used in [`ModularCurve.mem_regularDifferentialsBar_of_coeffMap_diffQExpBar_eq_qExpansion`](thm.html#ModularCurve.mem_regularDifferentialsBar_of_coeffMap_diffQExpBar_eq_qExpansion).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_ordDiff_smul_D_coeffEmb_jq_nonneg_iff.lean

import Definitions.Def_AlgebraicCurve_Differentials
import Definitions.Def_ModularCurve_QAdicPlace
import Definitions.Def_ModularCurve_LaurentCoeff

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve AlgebraicCurve

theorem ModularCurve.ordDiff_smul_D_coeffEmb_jq_nonneg_iff (K : Type*) [Field K] [Algebra ℚ K] (N : ℕ) [NeZero N] (w : Place K (laurentBaseChange K (modularFunctionFieldFull N)))
    (hw : w.ord ⟨coeffEmb K jq, coeffEmb_mem_laurentBaseChange K (jq_mem_full N)⟩ ≠ 0)
    (x : laurentBaseChange K (modularFunctionFieldFull N)) (hx : x ≠ 0) :
    0 ≤ w.ordDiff (x • KaehlerDifferential.D K (laurentBaseChange K (modularFunctionFieldFull N))
        ⟨coeffEmb K jq, coeffEmb_mem_laurentBaseChange K (jq_mem_full N)⟩) ↔
      1 - w.ord ⟨coeffEmb K jq, coeffEmb_mem_laurentBaseChange K (jq_mem_full N)⟩ ≤ w.ord x := by sorry
