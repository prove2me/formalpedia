-- Prove2me | Theorems.Thm_LaurentSeries_injective_of_forall_apply_tmul_eq_smul_map
-- name    : LaurentSeries.injective_of_forall_apply_tmul_eq_smul_map
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:11.015121+00:00
-- url     : https://prove2.me/theorems/0ca52107-0e01-5f81-9cca-763e3997e39c
-- title:
--   Injectivity of K ⊗_k k((q)) → K((q))
-- statement:
--   Let $k$ and $K$ be fields with $K$ a $k$-algebra, and let $\Phi \colon K \otimes_k \mathrm{LaurentSeries}\,k \to \mathrm{LaurentSeries}\,K$ be a $k$-linear map between the indicated $k$-modules, where $\mathrm{LaurentSeries}$ denotes Mathlib's formal Laurent series, i.e. Hahn series with value group $\mathbb{Z}$. Assume that $\Phi$ has the expected effect on pure tensors: for every $a \in K$ and every $f \in \mathrm{LaurentSeries}\,k$, one has $\Phi(a \otimes f) = a \cdot f^{K}$, where $f^{K}$ is the Laurent series over $K$ obtained by applying the structure map $k \to K$ to each coefficient of $f$, and the product is scalar multiplication by $a$ on $\mathrm{LaurentSeries}\,K$. The conclusion is that $\Phi$ is injective as a function. Thus the multiplication map from $K \otimes_k k(\!(q)\!)$ to $K(\!(q)\!)$ — which is determined on pure tensors by the stated hypothesis — has trivial kernel; the statement is formulated for the $k$-linear map only, with no ring or algebra structure on the tensor product required.
--
--   This is the linear disjointness of $k(\!(q)\!)$ and $K$ over $k$ inside $K(\!(q)\!)$: a $q$-expansion over $K$ coming from the tensor product determines its components uniquely. It is used in the treatment of $q$-expansions of cusp forms under the diamond and Atkin–Lehner operators, and in identifying kernels of reduction maps on modular curves via spans of tensors.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LaurentSeries_injective_of_forall_apply_tmul_eq_smul_map.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct

universe u v

theorem LaurentSeries.injective_of_forall_apply_tmul_eq_smul_map
    (k : Type u) (K : Type v) [Field k] [Field K] [Algebra k K]
    (Φ : K ⊗[k] LaurentSeries k →ₗ[k] LaurentSeries K)
    (hΦ : ∀ (a : K) (f : LaurentSeries k), Φ (a ⊗ₜ[k] f) = a • f.map (algebraMap k K)) :
    Function.Injective Φ := by sorry
