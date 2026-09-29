-- Prove2me | Theorems.Thm_IsIntegral_of_mem_span_of_apply_eq_smul
-- name    : IsIntegral.of_mem_span_of_apply_eq_smul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.878306+00:00
-- url     : https://prove2.me/theorems/144e8b96-09bc-5264-9ebd-b4c58cdd3cb2
-- title:
--   Eigenvalues on a finitely generated ℤ-lattice are integral
-- statement:
--   Let $V$ be an additive commutative group carrying a $\mathbb{C}$-module structure, let $L$ be a $\mathbb{Z}$-submodule of $V$ which is finitely generated (`L.FG`), and let $T : V \to V$ be a $\mathbb{C}$-linear endomorphism which maps $L$ into itself, in the sense that $T x \in L$ for every $x \in L$. Let $v \in V$ lie in the $\mathbb{C}$-span of the underlying set of $L$, suppose $v \neq 0$, and suppose that $T v = c \cdot v$ for a scalar $c \in \mathbb{C}$. The conclusion is that $c$ is integral over $\mathbb{Z}$, i.e. `IsIntegral ℤ c`: there is a monic polynomial with integer coefficients vanishing at $c$, so $c$ is an algebraic integer. No freeness of $L$, no linear independence of a generating set, and no assumption that $v$ itself lies in $L$ are required; only that $v$ is a nonzero element of the complex span of $L$.
--
--   This is the standard integrality criterion for an eigenvalue of an operator stabilising a finitely generated $\mathbb{Z}$-lattice, in the form obtained from Cayley–Hamilton over $\mathbb{Z}$ rather than from the determinant trick. It is used to show that the $q$-expansion coefficients of a normalised eigenform are algebraic integers, via [`CuspForm.IsNormalizedEigenform.exists_integralClosure_coe_eq_qCoeff`](thm.html#CuspForm.IsNormalizedEigenform.exists_integralClosure_coe_eq_qCoeff).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IsIntegral_of_mem_span_of_apply_eq_smul.lean

import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem IsIntegral.of_mem_span_of_apply_eq_smul {V : Type*} [AddCommGroup V] [Module ℂ V] (L : Submodule ℤ V) (hfg : L.FG) (T : V →ₗ[ℂ] V) (hTL : ∀ x ∈ L, T x ∈ L) {v : V} (hv : v ∈ Submodule.span ℂ (L : Set V)) (hv0 : v ≠ 0) {c : ℂ} (hTv : T v = c • v) : IsIntegral ℤ c := by sorry
