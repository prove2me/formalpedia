-- Prove2me | Theorems.Thm_IntermediateField_apply_algebraMap_eq_and_norm_apply_eq_of_ringEquiv_of_padic
-- name    : IntermediateField.apply_algebraMap_eq_and_norm_apply_eq_of_ringEquiv_of_padic
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.515241+00:00
-- url     : https://prove2.me/theorems/9710187d-f232-5da3-9735-9594e019cac0
-- title:
--   Ring isomorphisms of finite extensions of ℚ_q are ℚ_q-linear isometries
-- statement:
--   Let $q$ be a prime number and let `PadicAlgCl q` be the algebraic closure of $\mathbb{Q}_q$ used throughout, with its absolute value $\|\cdot\|$. Let $L_1$ and $L_2$ be intermediate fields of the extension $\mathbb{Q}_q \subseteq$ `PadicAlgCl q`, each assumed finite-dimensional as a $\mathbb{Q}_q$-vector space, and let $\alpha : L_1 \to L_2$ be a ring isomorphism, that is, a bijection respecting addition and multiplication only; no continuity, no $\mathbb{Q}_q$-linearity and no compatibility with the ambient absolute value is assumed. The conclusion is the conjunction of two assertions. First, $\alpha$ restricts to the identity on the base field: for every $x \in \mathbb{Q}_q$, the image under $\alpha$ of the element of $L_1$ determined by $x$ via the structure map $\mathbb{Q}_q \to L_1$ is the element of $L_2$ determined by $x$ via the structure map $\mathbb{Q}_q \to L_2$. Second, $\alpha$ is an isometry for the absolute value inherited from `PadicAlgCl q`: for every $x \in L_1$, the norm of the image of $\alpha(x)$ in `PadicAlgCl q` equals the norm of the image of $x$ in `PadicAlgCl q`.
--
--   This is the rigidity (automatic continuity) statement for $q$-adic fields: an abstract ring isomorphism between two finite extensions of $\mathbb{Q}_q$ inside a fixed algebraic closure is automatically $\mathbb{Q}_q$-linear and norm-preserving, because the valuation ring is characterised by purely multiplicative divisibility conditions. It is used in the local place-decomposition bookkeeping, in [`NumberField.PlaceDecomp.inflate_sub_unitsInflate2_carryFun_mem_levelCoboundaries2`](thm.html#NumberField.PlaceDecomp.inflate_sub_unitsInflate2_carryFun_mem_levelCoboundaries2), to transport norms along isomorphisms of local fields that are produced without continuity data.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IntermediateField_apply_algebraMap_eq_and_norm_apply_eq_of_ringEquiv_of_padic.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem IntermediateField.apply_algebraMap_eq_and_norm_apply_eq_of_ringEquiv_of_padic
    (q : ℕ) [Fact q.Prime]
    (L₁ L₂ : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] L₁] [FiniteDimensional ℚ_[q] L₂]
    (α : L₁ ≃+* L₂) :
    (∀ x : ℚ_[q], α (algebraMap ℚ_[q] L₁ x) = algebraMap ℚ_[q] L₂ x) ∧
    (∀ x : L₁, ‖((α x : L₂) : PadicAlgCl q)‖ = ‖(x : PadicAlgCl q)‖) := by sorry
