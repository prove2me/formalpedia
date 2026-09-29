-- Prove2me | Theorems.Thm_MeasureTheory_addEquivAddHaarChar_eq_one_and_measurePreserving_of_isAddFundamentalDomain_of_forall_apply_mem_iff
-- name    : MeasureTheory.addEquivAddHaarChar_eq_one_and_measurePreserving_of_isAddFundamentalDomain_of_forall_apply_mem_iff
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:12.429051+00:00
-- url     : https://prove2.me/theorems/fdb646a0-4f12-5440-ac49-06093aeb9a98
-- title:
--   Automorphism stabilising a lattice has Haar character one
-- statement:
--   Let $G$ be an additive group with a topology making it a topological additive group, locally compact, equipped with its Borel $\sigma$-algebra as measurable space structure. Let $\mu$ be a measure on $G$ which is an additive Haar measure and is regular, let $\Gamma$ be a countable additive subgroup of $G$, and let $F \subseteq G$ be a set which is an additive fundamental domain for $\Gamma$ acting on $G$ by translation with respect to $\mu$ (that is, $F$ is null measurable and almost every point of $G$ has exactly one $\Gamma$-translate lying in $F$), with $\mu(F) \neq \infty$. Let $\varphi : G \to G$ be an isomorphism of additive groups which is a homeomorphism, and suppose that for every $x \in G$ one has $\varphi(x) \in \Gamma$ if and only if $x \in \Gamma$. Then the additive Haar character of $\varphi$ — the scalar $c \in \mathbb{R}_{\geq 0}$ characterised by $c \cdot \varphi_{*}\mu = \mu$ — equals $1$, and $\varphi$ is measure preserving from $\mu$ to $\mu$."
--
--   This is the classical statement that a bicontinuous automorphism of a locally compact abelian group which stabilises a lattice of finite covolume has modulus $1$, hence preserves Haar measure. It is used in the estimates for automorphic forms, in the bounds [`AutomorphicForm.exists_forall_norm_finsum_borel_div_mem_sub_constantTerm_centralScalar_mul_le_inv_adelicHeight_pow`](thm.html#AutomorphicForm.exists_forall_norm_finsum_borel_div_mem_sub_constantTerm_centralScalar_mul_le_inv_adelicHeight_pow) and [`AutomorphicForm.exists_forall_norm_twistedBorelKernel_sub_constantTerm_centralScalar_mul_le_inv_adelicHeight_pow`](thm.html#AutomorphicForm.exists_forall_norm_twistedBorelKernel_sub_constantTerm_centralScalar_mul_le_inv_adelicHeight_pow), where invariance of a Haar measure under a lattice-preserving automorphism is needed.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_MeasureTheory_addEquivAddHaarChar_eq_one_and_measurePreserving_of_isAddFundamentalDomain_of_forall_apply_mem_iff.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory

theorem MeasureTheory.addEquivAddHaarChar_eq_one_and_measurePreserving_of_isAddFundamentalDomain_of_forall_apply_mem_iff
    {G : Type*} [AddGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G] [LocallyCompactSpace G]
    [MeasurableSpace G] [BorelSpace G]
    (μ : MeasureTheory.Measure G) [μ.IsAddHaarMeasure] [μ.Regular]
    (Γ : AddSubgroup G) [Countable Γ] (F : Set G) (hF : MeasureTheory.IsAddFundamentalDomain Γ F μ)
    (hFtop : μ F ≠ ⊤) (φ : G ≃ₜ+ G) (hφ : ∀ x : G, φ x ∈ Γ ↔ x ∈ Γ) :
    MeasureTheory.addEquivAddHaarChar φ = 1 ∧ MeasureTheory.MeasurePreserving φ μ μ := by sorry
