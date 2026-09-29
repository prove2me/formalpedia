-- Prove2me | Theorems.Thm_ModularCurve_exists_algHom_tensorProduct_modularFunctionFieldC_injective
-- name    : ModularCurve.exists_algHom_tensorProduct_modularFunctionFieldC_injective
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.209688+00:00
-- url     : https://prove2.me/theorems/b7a79e37-ff54-561d-9305-0cfc905c99a9
-- title:
--   Base change of the modular function field inside κ((q))
-- statement:
--   Let $\kappa_0$ and $\kappa$ be fields with $\kappa$ a $\kappa_0$-algebra, and let $N$ be a nonzero natural number. Inside the Laurent series field $K(\!(q)\!)$ over a field $K$ write $\tilde\jmath_K$ for `jqModC K`, the series $q^{-1}$ times the image in $K$ of the fixed integral power series `jNum` (the $q$-expansion of $j$), and $\tilde\jmath_{K,N}$ for `jqNModC K N`, obtained from $\tilde\jmath_K$ by the substitution $q \mapsto q^N$ given by `qExpand K N`; let `modularFunctionFieldC K N` be the intermediate field $K(\tilde\jmath_K, \tilde\jmath_{K,N})$ of $K(\!(q)\!)$ generated over $K$ by these two elements. The assertion is that there exists a $\kappa$-algebra homomorphism $f$ from $\kappa \otimes_{\kappa_0} \,$`modularFunctionFieldC κ₀ N` to $\kappa(\!(q)\!)$ with four properties: on pure tensors $f(x \otimes g) = x \cdot g^{(\kappa)}$, where $g^{(\kappa)}$ is the Laurent series obtained from $g$ by applying $\kappa_0 \to \kappa$ to each coefficient (`coeffMap`); $f$ is injective; every value of $f$ lies in `modularFunctionFieldC κ N`; and every $y \in$ `modularFunctionFieldC κ N` admits elements $a, b$ of the tensor product with $f(b) \neq 0$ and $y \cdot f(b) = f(a)$, so that $\kappa(\tilde\jmath_\kappa, \tilde\jmath_{\kappa,N})$ is the fraction field of the image of $f$.
--
--   This is the base-change statement for the modular function field of level structure $\Gamma$ of the $j$, $j(q^N)$ type along an arbitrary extension of base fields, with no hypothesis on $\kappa_0$ (in particular positive characteristic is allowed); it expresses that $\kappa$ and $\kappa_0(\tilde\jmath,\tilde\jmath_N)$ are linearly disjoint over $\kappa_0$ inside $\kappa(\!(q)\!)$ and that the tensor product has the right fraction field. It serves as the ring-theoretic transport device for identifying function fields of geometric fibres of the Deligne–Rapoport modular curves, and is used by [`ModularCurve.DRLevel.exists_curveModel_iso_fibre0_chartPin_of_ringHom`](thm.html#ModularCurve.DRLevel.exists_curveModel_iso_fibre0_chartPin_of_ringHom).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_algHom_tensorProduct_modularFunctionFieldC_injective.lean

import Mathlib
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_LaurentCoeff

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct

theorem ModularCurve.exists_algHom_tensorProduct_modularFunctionFieldC_injective
    (κ₀ κ : Type*) [Field κ₀] [Field κ] [Algebra κ₀ κ] (N : ℕ) [NeZero N] :
    ∃ f : κ ⊗[κ₀] ↥(modularFunctionFieldC κ₀ N) →ₐ[κ] LaurentSeries κ,
      (∀ (x : κ) (g : ↥(modularFunctionFieldC κ₀ N)),
          f (x ⊗ₜ[κ₀] g) = x • ModularCurve.coeffMap (algebraMap κ₀ κ) (g : LaurentSeries κ₀)) ∧
      Function.Injective f ∧
      (∀ z, f z ∈ modularFunctionFieldC κ N) ∧
      (∀ y ∈ modularFunctionFieldC κ N, ∃ a b, f b ≠ 0 ∧ y * f b = f a) := by sorry
