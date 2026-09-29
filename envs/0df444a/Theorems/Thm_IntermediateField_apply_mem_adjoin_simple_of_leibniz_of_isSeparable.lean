-- Prove2me | Theorems.Thm_IntermediateField_apply_mem_adjoin_simple_of_leibniz_of_isSeparable
-- name    : IntermediateField.apply_mem_adjoin_simple_of_leibniz_of_isSeparable
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.515241+00:00
-- url     : https://prove2.me/theorems/2543a067-8d72-5a67-8fad-029397f84213
-- title:
--   Derivations stable on F are stable on F(α), α separable
-- statement:
--   Let $K$ and $L$ be fields with $L$ a $K$-algebra, and let $D \colon L \to L$ be a function of sets which is additive, $D(a+b) = D a + D b$ for all $a, b \in L$, and satisfies the Leibniz rule $D(ab) = a\,D b + b\,D a$ for all $a, b \in L$; no compatibility with the $K$-structure, and in particular no $K$-linearity, is assumed. Let $F$ be an intermediate field of $L/K$ which is stable under $D$, in the sense that $D x \in F$ for every $x \in L$ with $x \in F$, and let $\alpha \in L$ be separable over $F$, i.e. the minimal polynomial of $\alpha$ over $F$ is a separable polynomial (so in particular $\alpha$ is algebraic over $F$). Then for every $x \in L$ lying in the intermediate field $F(\alpha)$ obtained by adjoining the singleton $\{\alpha\}$ to $F$ inside $L$, the element $D x$ again lies in $F(\alpha)$. Thus the subfield $F(\alpha)$ of $L$ is stable under $D$.
--
--   This is the standard extension-of-derivations statement for simple separable extensions, in the form of stability of $F(\alpha)$ under a given additive Leibniz map on the ambient field. It is used in the construction of the modular function field, where it shows that a field generated over a $D$-stable subfield by a separable element remains stable under the relevant logarithmic-derivative operator, via [`ModularCurve.thetaL_div_thetaL_jqModC_mem_modularFunctionFieldC`](thm.html#ModularCurve.thetaL_div_thetaL_jqModC_mem_modularFunctionFieldC).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IntermediateField_apply_mem_adjoin_simple_of_leibniz_of_isSeparable.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem IntermediateField.apply_mem_adjoin_simple_of_leibniz_of_isSeparable
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (D : L → L) (hadd : ∀ a b : L, D (a + b) = D a + D b) (hmul : ∀ a b : L, D (a * b) = a * D b + b * D a)
    (F : IntermediateField K L) (hF : ∀ x : L, x ∈ F → D x ∈ F)
    (α : L) (hα : IsSeparable F α) (x : L) (hx : x ∈ IntermediateField.adjoin F ({α} : Set L)) :
    D x ∈ IntermediateField.adjoin F ({α} : Set L) := by sorry
