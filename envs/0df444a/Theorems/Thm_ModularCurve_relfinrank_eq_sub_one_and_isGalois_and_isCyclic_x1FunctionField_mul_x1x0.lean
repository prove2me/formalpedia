-- Prove2me | Theorems.Thm_ModularCurve_relfinrank_eq_sub_one_and_isGalois_and_isCyclic_x1FunctionField_mul_x1x0
-- name    : ModularCurve.relfinrank_eq_sub_one_and_isGalois_and_isCyclic_x1FunctionField_mul_x1x0
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:54.618386+00:00
-- url     : https://prove2.me/theorems/f52b8738-caf3-5af0-b4b9-f150db33393e
-- title:
--   Cyclic degree p-1 Galois extension of modular function fields
-- statement:
--   Let $p$ be a prime and $M$ a nonzero natural number with $5 \le M$ and $p \nmid M$, and let $L$ be a field of characteristic zero. Inside the Laurent series field $L((q))$ consider two intermediate fields of $L \subseteq L((q))$: the field $K$, assumed equal to [`ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p))`](def/ModularCurve_LaurentCoeff.html#L103), that is the subfield of $L((q))$ generated over $L$ by the image, under the coefficientwise map $\mathbb{Q}((q)) \to L((q))$ induced by $\mathbb{Q} \to L$, of the subfield of $\mathbb{Q}((q))$ generated over $\mathbb{Q}$ by the set `intFormRatiosC ℚ (Gamma1 (M * p))`; and the field $K_1$, assumed equal to [`ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ M p)`](def/ModularCurve_LaurentCoeff.html#L103), obtained in the same way from the subfield of $\mathbb{Q}((q))$ generated over $\mathbb{Q}$ by `intFormRatiosC ℚ (Gamma1 M ⊓ Gamma0 p)`. Assume $K_1 \le K$. Then the relative finrank of $K$ over $K_1$ equals $p - 1$ (natural-number subtraction); moreover, $K$ regarded as an extension field of $K_1$ via `IntermediateField.extendScalars` is Galois over $K_1$, and its group of $K_1$-algebra automorphisms is cyclic.
--
--   This is the statement that the covering of modular curves $X_1(Mp) \to X_{\Gamma_1(M) \cap \Gamma_0(p)}$ is cyclic Galois of degree $p-1$, realised on the level of $q$-expansion function fields after base change from $\mathbb{Q}$ to an arbitrary field of characteristic zero; classically the Galois group is $(\mathbb{Z}/p)^\times$ acting through the diamond automorphisms $\langle d\rangle$ with $d \equiv 1 \bmod M$. It feeds the analysis of integral models of $X_1(Mp)$ and of their fibres, in particular the comparison of charts and the computation of completed local rings at non-regular points.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_relfinrank_eq_sub_one_and_isGalois_and_isCyclic_x1FunctionField_mul_x1x0.lean

import Mathlib
import Definitions.Def_ModularCurve_X1

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ModularCurve.relfinrank_eq_sub_one_and_isGalois_and_isCyclic_x1FunctionField_mul_x1x0
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hM : 5 ≤ M) (hpM : ¬ p ∣ M)
    (L : Type) [Field L] [CharZero L]
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p)))
    (K₁ : IntermediateField L (LaurentSeries L))
    (hK₁ : K₁ = ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ M p))
    (hle : K₁ ≤ K) :
    IntermediateField.relfinrank K₁ K = p - 1 ∧
      IsGalois ↥K₁ ↥(IntermediateField.extendScalars hle) ∧
      IsCyclic (↥(IntermediateField.extendScalars hle) ≃ₐ[↥K₁] ↥(IntermediateField.extendScalars hle)) := by sorry
