-- Prove2me | Theorems.Thm_ModularCurve_laurentBaseChange_eq_adjoin_image_coeffMap_and_exists_ringHom
-- name    : ModularCurve.laurentBaseChange_eq_adjoin_image_coeffMap_and_exists_ringHom
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.34379+00:00
-- url     : https://prove2.me/theorems/c1de1a31-d5dc-5c06-a33b-cb62bbf55de1
-- title:
--   Base change of Laurent subfields along a field homomorphism
-- statement:
--   Let $L_0$ and $L$ be fields of characteristic zero (so each carries its canonical $\mathbb{Q}$-algebra structure), let $i : L_0 \to L$ be a ring homomorphism, and write $\mathrm{coeffMap}\,i : L_0(\!(q)\!) \to L(\!(q)\!)$ for the ring homomorphism applying $i$ to each coefficient of a Laurent series, and $\mathrm{coeffEmb}\,M : \mathbb{Q}(\!(q)\!) \to M(\!(q)\!)$ for the analogous coefficientwise map induced by $\mathbb{Q} \to M$. Let $F_0$ be an intermediate field of $\mathbb{Q} \subseteq \mathbb{Q}(\!(q)\!)$. Let $K_0$ be an intermediate field of $L_0 \subseteq L_0(\!(q)\!)$ equal to the base change $\mathrm{laurentBaseChange}\,L_0\,F_0$, i.e. the intermediate field generated over $L_0$ by $\mathrm{coeffEmb}\,L_0(F_0)$, and let $K$ be an intermediate field of $L \subseteq L(\!(q)\!)$ equal to $\mathrm{laurentBaseChange}\,L\,F_0$, the intermediate field generated over $L$ by $\mathrm{coeffEmb}\,L(F_0)$. The conclusion is twofold: first, $K$ coincides with the intermediate field generated over $L$ by the coefficientwise image $(\mathrm{coeffMap}\,i)(K_0)$ inside $L(\!(q)\!)$; second, there exists a ring homomorphism $c_K : K_0 \to K$ such that for every $x \in K_0$ the Laurent series underlying $c_K(x)$ is $\mathrm{coeffMap}\,i$ applied to the Laurent series underlying $x$, so $c_K$ is the restriction of the coefficientwise map.
--
--   This records the functoriality of the construction $F_0 \mapsto L \cdot F_0$ attaching to a field of rational $q$-expansions its base change to a larger constant field: the formation of the compositum commutes with coefficientwise extension of constants, and the coefficientwise map restricts to a homomorphism of the base-changed fields. It is used in the construction of charts and of completions of local rings on modular curves after base change, where a comparison map between the function fields over two constant fields is needed.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_laurentBaseChange_eq_adjoin_image_coeffMap_and_exists_ringHom.lean

import Mathlib
import Definitions.Def_ModularCurve_LaurentCoeff

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ModularCurve.laurentBaseChange_eq_adjoin_image_coeffMap_and_exists_ringHom
    (L₀ : Type) [Field L₀] [CharZero L₀] (L : Type) [Field L] [CharZero L] (i : L₀ →+* L)
    (F₀ : IntermediateField ℚ (LaurentSeries ℚ))
    (K₀ : IntermediateField L₀ (LaurentSeries L₀)) (hK₀ : K₀ = ModularCurve.laurentBaseChange L₀ F₀)
    (K : IntermediateField L (LaurentSeries L)) (hK : K = ModularCurve.laurentBaseChange L F₀) :
    K = IntermediateField.adjoin L (⇑(ModularCurve.coeffMap i) '' (K₀ : Set (LaurentSeries L₀))) ∧
    ∃ cK : ↥K₀ →+* ↥K, ∀ x : ↥K₀,
      ((cK x : ↥K) : LaurentSeries L) = ModularCurve.coeffMap i ((x : ↥K₀) : LaurentSeries L₀) := by sorry
