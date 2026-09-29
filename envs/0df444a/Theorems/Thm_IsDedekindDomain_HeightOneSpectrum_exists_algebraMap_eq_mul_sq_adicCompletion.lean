-- Prove2me | Theorems.Thm_IsDedekindDomain_HeightOneSpectrum_exists_algebraMap_eq_mul_sq_adicCompletion
-- name    : IsDedekindDomain.HeightOneSpectrum.exists_algebraMap_eq_mul_sq_adicCompletion
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.515241+00:00
-- url     : https://prove2.me/theorems/8e566f3d-5850-5a5e-826e-6b9f75b6cc77
-- title:
--   Global representatives for square classes of Kᵥ^×
-- statement:
--   Let $K$ be a number field (a field of characteristic $0$ that is finite-dimensional over $\mathbb{Q}$, in Mathlib's sense), let $v$ be a point of the height-one spectrum of the ring of integers $\mathcal{O}_K$, i.e. a nonzero prime ideal of $\mathcal{O}_K$, and let $v.\mathrm{adicCompletion}\,K$ denote the completion $K_v$ of $K$ with respect to the $v$-adic valuation. The assertion is that for every element $d$ of $K_v$ with $d \neq 0$ there exist an element $d'$ of $K$ and an element $c$ of $K_v$ such that $c \neq 0$ and the image of $d'$ under the canonical algebra map $K \to K_v$ equals $d \cdot c^{2}$. Thus every nonzero element of $K_v$ becomes, after multiplication by a square of $K_v^\times$, the image of a global element; equivalently the map $K^\times \to K_v^\times / (K_v^\times)^2$ is surjective, the nonvanishing of $d'$ being implicit in the equation since $d$ and $c$ are nonzero.
--
--   This is the standard fact that $K$ meets every square class of $K_v^\times$, a consequence of the density of $K$ in $K_v$ together with the openness of the subgroup of squares. It is used in [`AutomorphicForm.exists_isNormOf_of_isField_tensor_adicCompletion_of_not_isSquare_discr_of_finrank_dvd`](thm.html#AutomorphicForm.exists_isNormOf_of_isField_tensor_adicCompletion_of_not_isSquare_discr_of_finrank_dvd) to realise a quadratic extension of $K_v$ as the completion of a quadratic extension of $K$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IsDedekindDomain_HeightOneSpectrum_exists_algebraMap_eq_mul_sq_adicCompletion.lean

import Definitions.Def_DedekindDomain_Completion_BaseChange

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open scoped Polynomial

theorem IsDedekindDomain.HeightOneSpectrum.exists_algebraMap_eq_mul_sq_adicCompletion
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    (d : v.adicCompletion K) (hd : d ≠ 0) :
    ∃ (d' : K) (c : v.adicCompletion K), c ≠ 0 ∧ algebraMap K (v.adicCompletion K) d' = d * c ^ 2 := by sorry
