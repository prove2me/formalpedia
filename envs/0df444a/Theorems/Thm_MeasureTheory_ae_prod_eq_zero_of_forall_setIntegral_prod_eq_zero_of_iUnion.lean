-- Prove2me | Theorems.Thm_MeasureTheory_ae_prod_eq_zero_of_forall_setIntegral_prod_eq_zero_of_iUnion
-- name    : MeasureTheory.ae_prod_eq_zero_of_forall_setIntegral_prod_eq_zero_of_iUnion
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:12.429051+00:00
-- url     : https://prove2.me/theorems/9c7ead6b-9e3a-5321-8347-d2d454b8c7a5
-- title:
--   Kernels vanishing on rectangles in an exhaustion vanish a.e.
-- statement:
--   Let $X$ be a measurable space and $\mu$ an s-finite measure on $X$, and let $k \colon X \times X \to \mathbb{C}$ be a function. Let $(S_n)_{n \in \mathbb{N}}$ be a sequence of subsets of $X$ such that each $S_n$ is measurable, the sequence is monotone (increasing with respect to inclusion), and $\mu$-almost every $x \in X$ lies in $\bigcup_n S_n$. Assume further that for every $n$ the function $k$ is integrable on the rectangle $S_n \times S_n$ with respect to the product measure $\mu \otimes \mu$, and that for every $n$ and all measurable sets $A, B \subseteq S_n$ one has $\int_{A \times B} k \, d(\mu \otimes \mu) = 0$. The conclusion is that $k = 0$ almost everywhere with respect to $\mu \otimes \mu$, i.e. $k$ agrees with the zero function on the complement of a $(\mu \otimes \mu)$-null subset of $X \times X$.
--
--   This is the uniqueness statement for a locally integrable integral kernel in terms of its matrix coefficients against indicator functions: vanishing weakly on all measurable rectangles inside an exhaustion of $X$ forces the kernel to vanish almost everywhere. It is used in the automorphic-forms layer of the development, where an identity between kernels is established first against indicators on the pieces of a truncation exhaustion.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_MeasureTheory_ae_prod_eq_zero_of_forall_setIntegral_prod_eq_zero_of_iUnion.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory

theorem MeasureTheory.ae_prod_eq_zero_of_forall_setIntegral_prod_eq_zero_of_iUnion
    {X : Type*} [MeasurableSpace X] (μ : Measure X) [SFinite μ]
    (k : X × X → ℂ)
    (S : ℕ → Set X) (hS : ∀ n, MeasurableSet (S n)) (hmono : Monotone S)
    (hcov : ∀ᵐ x ∂μ, x ∈ ⋃ n, S n)
    (hint : ∀ n, IntegrableOn k (S n ×ˢ S n) (μ.prod μ))
    (hzero : ∀ n, ∀ A ⊆ S n, MeasurableSet A → ∀ B ⊆ S n, MeasurableSet B →
      ∫ p in A ×ˢ B, k p ∂(μ.prod μ) = 0) :
    k =ᵐ[μ.prod μ] 0 := by sorry
