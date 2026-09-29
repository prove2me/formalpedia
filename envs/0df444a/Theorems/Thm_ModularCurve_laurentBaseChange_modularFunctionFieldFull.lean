-- Prove2me | Theorems.Thm_ModularCurve_laurentBaseChange_modularFunctionFieldFull
-- name    : ModularCurve.laurentBaseChange_modularFunctionFieldFull
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.34379+00:00
-- url     : https://prove2.me/theorems/46aa8042-66c4-5557-9b26-2d101ec70a03
-- title:
--   Base change of the full modular function field to L
-- statement:
--   Let $L$ be a field of characteristic zero, i.e. a field equipped with a $\mathbb{Q}$-algebra structure, and let $N$ be a nonzero natural number. On the $\mathbb{Q}$-side, [`ModularCurve.modularFunctionFieldFull N`](def/ModularCurve_X0.html#L305) is the intermediate field of $\mathbb{Q}((q))$ generated over $\mathbb{Q}$ by the set `divisorExpansions N`, namely by the elements $\mathrm{qExpand}\,\mathbb{Q}\,d\,(jq)$ for all nonzero $d$ dividing $N$, where $\mathrm{qExpand}\,d$ is the ring endomorphism of a Laurent series field substituting $q \mapsto q^{d}$ (domain embedding along multiplication by $d$ on $\mathbb{Z}$). Its base change [`ModularCurve.laurentBaseChange L`](def/ModularCurve_LaurentCoeff.html#L103) is the intermediate field of $L((q))$ generated over $L$ by the image of this field under `coeffEmb L`, the coefficientwise ring homomorphism $\mathbb{Q}((q)) \to L((q))$ induced by $\mathbb{Q} \to L$. The theorem asserts that this base-changed field is equal to the intermediate field of $L((q))$ generated over $L$ by the set of all [`ModularCurve.jqNModC L d`](def/ModularCurve_JqCoeff.html#L18) with $d$ nonzero and $d \mid N$, where $\mathrm{jqNModC}\,L\,d = \mathrm{qExpand}\,L\,d$ applied to $\mathrm{jqModC}\,L = q^{-1}\cdot(\text{the } j\text{-numerator power series with coefficients mapped into } L)$.
--
--   This identifies the base change to $L$ of the function field $\mathbb{Q}(j(q^{d}) : d \mid N)$ attached to $X_0(N)$-type data as the field generated over $L$ by the corresponding divisor expansions with $L$-coefficients, so that subsequent work with degeneracy maps, Hecke correspondences and $j$-charts can be carried out directly over $L$. It is used in the construction of integral lifts of $j$-charts, in degree computations for the generators $\bar{j}$, and in the comparison of $q$-expansions under slash operators.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_laurentBaseChange_modularFunctionFieldFull.lean

import Definitions.Def_ModularCurve_LaurentCoeff
import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularCurve_JqCoeff

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ModularCurve.laurentBaseChange_modularFunctionFieldFull (L : Type*) [Field L] [Algebra ℚ L] (N : ℕ) [NeZero N] : ModularCurve.laurentBaseChange L (ModularCurve.modularFunctionFieldFull N) = IntermediateField.adjoin L {x | ∃ (d : ℕ) (_ : NeZero d), d ∣ N ∧ x = ModularCurve.jqNModC L d} := by sorry
