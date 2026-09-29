-- Prove2me | Theorems.Thm_ModularForm_exists_mul_eq_mul_norm_of_forall_slash_mul_eq
-- name    : ModularForm.exists_mul_eq_mul_norm_of_forall_slash_mul_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.335791+00:00
-- url     : https://prove2.me/theorems/8f2eeab0-7d70-5b5e-8e24-570ab386093d
-- title:
--   H-invariant ratios of forms on G become ratios on H
-- statement:
--   Let $\mathcal G$ and $\mathcal H$ be subgroups of $\mathrm{GL}_2(\mathbb R)$ such that $\mathcal G$ has finite relative index in $\mathcal H$, i.e. $\mathcal G \cap \mathcal H$ has finite index in $\mathcal H$, and such that every element of $\mathcal H$ has determinant $\pm 1$. Let $k$ be an integer and let $F, G$ be modular forms of weight $k$ for $\mathcal G$. Assume that for every $h \in \mathcal H$ one has the identity of functions on the upper half-plane $$(F \mid_k h)\cdot G = F \cdot (G \mid_k h),$$ i.e. the ratio $F/G$ is formally invariant under the weight-$k$ slash action of $\mathcal H$. Write $d = \#\bigl(\mathcal H / (\mathcal G \cap \mathcal H)\bigr)$ for the cardinality of the coset space of $\mathcal G \cap \mathcal H$, viewed as a subgroup of $\mathcal H$, in $\mathcal H$. Then there exists a modular form $\Phi$ of weight $k\,d$ for $\mathcal H$ such that, as functions on the upper half-plane, $$\Phi \cdot G = F \cdot \mathrm{norm}_{\mathcal H}(G),$$ where $\mathrm{norm}_{\mathcal H}(G)$ is the norm of $G$ from $\mathcal G$ to $\mathcal H$, itself a modular form of weight $k\,d$ for $\mathcal H$. The conclusion asserts only the existence of such a $\Phi$, not any particular formula for it.
--
--   This is the classical device of symmetric functions of the translates: a quotient of modular forms on a subgroup of finite index which is invariant under a larger group $\mathcal H$ is already a quotient of two modular forms on $\mathcal H$, the denominator being the norm. It is used in the study of modular functions for full level structures, where invariance of a function under level automorphisms has to be converted into an honest ratio of forms on the larger group, and it is cited by the results on level automorphisms and $q$-expansions in that development.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularForm_exists_mul_eq_mul_norm_of_forall_slash_mul_eq.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped ModularForm

theorem ModularForm.exists_mul_eq_mul_norm_of_forall_slash_mul_eq
    (𝒢 ℋ : Subgroup (GL (Fin 2) ℝ)) [𝒢.IsFiniteRelIndex ℋ] [ℋ.HasDetPlusMinusOne] {k : ℤ}
    (F G : ModularForm 𝒢 k)
    (hFG : ∀ h ∈ ℋ, ((⇑F : UpperHalfPlane → ℂ) ∣[k] h) * (⇑G : UpperHalfPlane → ℂ) =
      (⇑F : UpperHalfPlane → ℂ) * ((⇑G : UpperHalfPlane → ℂ) ∣[k] h)) :
    ∃ Φ : ModularForm ℋ (k * Nat.card (ℋ ⧸ 𝒢.subgroupOf ℋ)),
      (⇑Φ : UpperHalfPlane → ℂ) * (⇑G : UpperHalfPlane → ℂ) =
        (⇑F : UpperHalfPlane → ℂ) * (⇑(ModularForm.norm ℋ G) : UpperHalfPlane → ℂ) := by sorry
