-- Prove2me | Theorems.Thm_ModularCurve_qExpand_mem_laurentBaseChange
-- name    : ModularCurve.qExpand_mem_laurentBaseChange
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:54.618386+00:00
-- url     : https://prove2.me/theorems/f962f4b7-dc1a-537d-801a-6ebdeae94842
-- title:
--   Substitution q↦ qⁿ commutes with base change of Laurent subfields
-- statement:
--   Let $L$ be a field equipped with a $\mathbb{Q}$-algebra structure, and let $n$ be a natural number with $n \neq 0$. Let $F_0$ and $F_1$ be intermediate fields of $\mathbb{Q}((q))/\mathbb{Q}$, where $\mathbb{Q}((q))$ is the field `LaurentSeries ℚ` of formal Laurent series, i.e. Hahn series over $\mathbb{Z}$. Write $\mathrm{qExpand}_R\,n$ for the ring endomorphism of $R((q))$ induced by the order-preserving injective map $g \mapsto n g$ on the exponent group $\mathbb{Z}$, that is, the substitution $q \mapsto q^n$, and write $\iota_L =$ `coeffEmb L` for the coefficientwise ring homomorphism $\mathbb{Q}((q)) \to L((q))$ obtained from $\mathbb{Q} \to L$. For an intermediate field $F$ of $\mathbb{Q}((q))/\mathbb{Q}$ let $L \cdot F =$ `laurentBaseChange L F` denote the intermediate field of $L((q))/L$ generated over $L$ by the image $\iota_L(F)$. Assume that $\mathrm{qExpand}_{\mathbb{Q}}\,n$ maps every element of $F_0$ into $F_1$. Then for every $x \in L \cdot F_0$ one has $\mathrm{qExpand}_L\,n\,x \in L \cdot F_1$.
--
--   The statement says that the substitution $q \mapsto q^n$ on Laurent series is compatible with extension of the field of coefficients at the level of generated subfields: a containment relation between two subfields of $\mathbb{Q}((q))$ propagates to the composita with $L$. It is used in the treatment of $q$-expansions of modular function fields, where $q \mapsto q^{\ell}$ realises one leg of a degeneracy map between levels after base change, and is invoked in the computation of degrees of such maps and in the analysis of $q$-expansions at full level.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_qExpand_mem_laurentBaseChange.lean

import Definitions.Def_ModularCurve_LaurentCoeff
import Definitions.Def_ModularCurve_X0

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ModularCurve.qExpand_mem_laurentBaseChange {L : Type*} [Field L] [Algebra ℚ L] {F₀ : IntermediateField ℚ (LaurentSeries ℚ)} (n : ℕ) [NeZero n] {F₁ : IntermediateField ℚ (LaurentSeries ℚ)} (hF : ∀ y ∈ F₀, ModularCurve.qExpand ℚ n y ∈ F₁) {x : LaurentSeries L} (hx : x ∈ ModularCurve.laurentBaseChange L F₀) : ModularCurve.qExpand L n x ∈ ModularCurve.laurentBaseChange L F₁ := by sorry
