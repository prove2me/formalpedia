-- Prove2me | Theorems.Thm_MatousekLP_SparseRecovery_good_iff_kernel_inter_cone
-- name    : MatousekLP.SparseRecovery.good_iff_kernel_inter_cone
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-03T13:39:16.149925+00:00
-- url     : https://prove2.me/theorems/63ac85ab-03ae-4f91-ad54-73335b45565a
-- title:
--   §8.5, p. 174 — L is good for z iff L ∩ C_z = {0}
-- statement:
--   Let $A$ be a real $m\times n$ matrix with kernel $L=\{x: Ax=0\}$, let $r\ge 0$, and let $z\in\mathbb{R}^n$ be a boundary point of the crosspolytope $B^n_1=\{x:\|x\|_1\le 1\}$, i.e. $\|z\|_1=1$, with $|\operatorname{supp}(z)|\le r$. Let
--   $$C_z=\{t(x-z):\ t\ge 0,\ x\in B^n_1\}.$$
--   Say that $L$ is good for $z$ if $(L+z)\cap B^n_1=\{z\}$. Then
--   $$(L+z)\cap B^n_1=\{z\}\iff L\cap C_z=\{0\}.$$
--
--   Together with Lemma 8.5.4, this recasts BP-exactness as the condition that the kernel avoids the cones $C_z$ at the sparse boundary points of the crosspolytope, which is the starting point of the probabilistic proofs of Theorem 8.5.2.
--
--   **Formalization Note** The hypotheses $\|z\|_1=1$ and $|\operatorname{supp}(z)|\le r$ are the book's "for $z$ as above"; $L$ is the kernel of $A$, as in the book's setting of a random matrix $A$.
-- source:
--   Matoušek & Gärtner, Understanding and Using Linear Programming, Springer 2007, p. 174, §8.5 "Intuition for BP-exactness" ("Then L good for z means exactly that L ∩ C_z = {0}")

import Mathlib
import Definitions.Def_MatousekLP_SparseRecovery_BasisPursuit

namespace MatousekLP.SparseRecovery

open Matrix

/-- **§8.5, p. 174** ("Intuition for BP-exactness"), Matoušek & Gärtner, *Understanding and
Using Linear Programming*, Springer 2007.  Let `z` be a boundary point of the crosspolytope
(`‖z‖₁ = 1`) with `|supp(z)| ≤ r`, and let `C_z = {t(x − z) : t ≥ 0, x ∈ B₁ⁿ}`.  Then "`L`
good for `z`" (`(L + z) ∩ B₁ⁿ = {z}`) "means exactly that `L ∩ C_z = {0}`", for `L` the
kernel of `A`. -/
theorem good_iff_kernel_inter_cone {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (r : ℕ)
    (z : Fin n → ℝ) (hz : l1Norm z = 1) (hsupp : (supp z).card ≤ r) :
    IsGoodFor (kernel A) z ↔ kernel A ∩ coneAt z = {0} := by sorry

end MatousekLP.SparseRecovery
