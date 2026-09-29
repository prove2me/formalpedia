-- Prove2me | Theorems.Thm_ModularCurve_diffQExpBar_injective_of_neZero
-- name    : ModularCurve.diffQExpBar_injective_of_neZero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:49.889759+00:00
-- url     : https://prove2.me/theorems/271acfec-a8a2-5baf-9ebc-aa1a2b2ffe5a
-- title:
--   Injectivity of the q-expansion map on differentials
-- statement:
--   Let $N$ be a nonzero natural number. Write $\bar L = \overline{\mathbb{Q}}$ for the algebraic closure of $\mathbb{Q}$, and let `modularFunctionFieldBar N` be the intermediate field of $\bar L((q))$ over $\bar L$ obtained as `laurentBaseChange` of `modularFunctionFieldFull N` along $\mathbb{Q} \to \bar L$, that is, the level-$N$ modular function field with coefficients extended to $\bar L$, realised inside the field of Laurent series in $q$ over $\bar L$. For an intermediate field $F$ of $\bar L((q))$ over $\bar L$, `diffQExp` is the $F$-linear map from the module of Kähler differentials $\Omega[F/\bar L]$ to $\bar L((q))$ obtained by lifting the derivation `qEulerOn F` (the Euler derivation $q\,\mathrm{d}/\mathrm{d}q$ on $F$, valued in Laurent series) through the universal derivation $D$; thus $f\,Dg \mapsto f \cdot q\,\mathrm{d}g/\mathrm{d}q$. The abbreviation `diffQExpBar N` is this map for $F =$ `modularFunctionFieldBar N`. The assertion is that `diffQExpBar N` is injective as a function on $\Omega[\,$`modularFunctionFieldBar N`$/\bar L\,]$.
--
--   In classical terms: a differential on the level-$N$ modular curve over $\overline{\mathbb{Q}}$ whose $q$-expansion at the cusp $\infty$ vanishes is itself zero, so differentials may be identified with their $q$-expansions. It is used in the computation of the space of holomorphic differentials and its integral lattice, and in the genus-versus-dimension comparison for weight-two cusp forms on $\Gamma_0$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_diffQExpBar_injective_of_neZero.lean

import Definitions.Def_ModularCurve_HeckeDifferential

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve

theorem ModularCurve.diffQExpBar_injective_of_neZero (N : ℕ) [NeZero N] :
    Function.Injective (diffQExpBar N) := by sorry
