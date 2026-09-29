-- Prove2me | Theorems.Thm_ModularCurve_exists_rational_basis_isModPFormFn_of_forall_coeffMap_mem
-- name    : ModularCurve.exists_rational_basis_isModPFormFn_of_forall_coeffMap_mem
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:51.361078+00:00
-- url     : https://prove2.me/theorems/ecb6352a-28dd-59da-80b0-3b3cd4df3842
-- title:
--   Rational basis for a Galois-stable space of q-expansions
-- statement:
--   Let $L$ be a field that is a finite Galois extension of $\mathbb{Q}$, let $F_0$ be an intermediate field of $\mathbb{Q} \subseteq \mathbb{Q}((q))$ (Laurent series over $\mathbb{Q}$), let $m$ be a natural number, and let $V$ be an $L$-submodule of $L((q))$ that is finite-dimensional over $L$. Assume: (i) for every $\mathbb{Q}$-algebra automorphism $\sigma$ of $L$ and every $x \in V$, the series obtained by applying $\sigma$ to each coefficient of $x$ (the ring homomorphism [`ModularCurve.coeffMap`](def/ModularCurve_LaurentCoeff.html#L16) attached to $\sigma$) again lies in $V$; (ii) every $x \in V$ lies in [`ModularCurve.laurentBaseChange L F₀`](def/ModularCurve_LaurentCoeff.html#L103), the intermediate field generated over $L$ inside $L((q))$ by the image of $F_0$ under the coefficientwise map [`ModularCurve.coeffEmb L`](def/ModularCurve_LaurentCoeff.html#L81) induced by $\mathbb{Q} \to L$; (iii) every $x \in V$ satisfies [`ModularCurve.IsModPFormFn L m`](def/ModularCurve_ModPFormFn.html#L20), that is, with $j =$ `jqModC L` the Laurent series $q^{-1}\cdot(\text{the } j\text{-numerator power series over } L)$, the element $x^6 j^{4m}(j-1728)^{3m}$ is integral over $L[j]$ and $x^2 j^{m}(j-1728)^{m}$ is integral over $L[j^{-1}]$. Then there are an $n$ and $Y : \mathrm{Fin}\,n \to \mathbb{Q}((q))$ such that each $Y_i$ lies in $F_0$, each $Y_i$ satisfies [`ModularCurve.IsModPFormFn ℚ m`](def/ModularCurve_ModPFormFn.html#L20), the family $Y$ is $\mathbb{Q}$-linearly independent, the family of coefficientwise images `coeffEmb L (Y i)` is $L$-linearly independent, and its $L$-span is exactly $V$.
--
--   This is the Galois-descent step which converts a finite-dimensional space of $q$-expansions over a number field $L$, stable under the coefficientwise Galois action, into a basis consisting of $q$-expansions with rational coefficients that still lie in $F_0$ and still satisfy the weight-$2m$ integrality conditions over $\mathbb{Q}$. It is used by [`ModularCurve.exists_linearIndependent_isModPFormFn_rat_dimFormula_le_card`](thm.html#ModularCurve.exists_linearIndependent_isModPFormFn_rat_dimFormula_le_card), where a dimension count performed over $L$ is transferred to $\mathbb{Q}$-rational functions.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_rational_basis_isModPFormFn_of_forall_coeffMap_mem.lean

import Mathlib
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_LaurentCoeff
import Definitions.Def_ModularCurve_ModPFormFn

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ModularCurve.exists_rational_basis_isModPFormFn_of_forall_coeffMap_mem
    (L : Type*) [Field L] [Algebra ℚ L] [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (F₀ : IntermediateField ℚ (LaurentSeries ℚ)) (m : ℕ)
    (V : Submodule L (LaurentSeries L)) [FiniteDimensional L V]
    (hV : ∀ (σ : L ≃ₐ[ℚ] L) (x : LaurentSeries L), x ∈ V → ModularCurve.coeffMap (σ : L →+* L) x ∈ V)
    (hVF : ∀ x ∈ V, x ∈ ModularCurve.laurentBaseChange L F₀)
    (hVB : ∀ x ∈ V, ModularCurve.IsModPFormFn L m x) :
    ∃ (n : ℕ) (Y : Fin n → LaurentSeries ℚ),
      (∀ i, Y i ∈ F₀) ∧ (∀ i, ModularCurve.IsModPFormFn ℚ m (Y i)) ∧ LinearIndependent ℚ Y ∧
      LinearIndependent L (fun i => ModularCurve.coeffEmb L (Y i)) ∧
      Submodule.span L (Set.range fun i => ModularCurve.coeffEmb L (Y i)) = V := by sorry
