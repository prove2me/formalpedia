-- Prove2me | Theorems.Thm_IsotropicSpin_norm_ZZ_YY
-- name    : IsotropicSpin.norm_ZZ_YY
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T04:26:30.531535+00:00
-- url     : https://prove2.me/theorems/7a929bf2-727f-457f-8b25-777353cb4d3e
-- title:
--   $\|ZZ^\dagger\|=\|YY^\dagger\|=1$ (p.3)
-- statement:
--   Let $S_1,S_2,S_3$ be the spin-1 matrices (13). Then
--
--   1. for all real $\alpha,\beta$, the matrix $Z$ of (19) satisfies $\|ZZ^\dagger\|=1$;
--   2. for every unit vector $\xi\in\mathbb C^3$, the matrix $Y=\sum_k\xi_kS_k$ of (18) satisfies $\|YY^\dagger\|=1$,
--
--   where $\|\cdot\|$ is the operator norm. With (17), this proves the bound (16) and hence (14).
--
--   **Formalization Note** The norm is the operator norm induced by the Euclidean norm on $\mathbb C^3$.
--
--   Differences from the source:
--   - generalization: Z of (19) with α ∈ [0, π] from (18) → every real α and β; reason: the identity holds for every α; specializes to α ∈ [0, π]
--   - encoding: operator norm ‖·‖ → the operator norm induced by the Euclidean norm on ℂ³ (scope Matrix.Norms.L2Operator); reason: the page says "operator norm" (p.2, before (16)); this is that norm
-- source:
--   Alicki, Isotropic quantum spin channels and additivity questions, arXiv:quant-ph/0402080v1, §2, proof of Theorem 1, sentence after (21), p.3

import Mathlib
import Definitions.Def_WHAdditivity_Renyi_Model
import Definitions.Def_IsotropicSpin_spinOne
import Definitions.Def_IsotropicSpin_yMat
import Definitions.Def_IsotropicSpin_zMat

open scoped Matrix Matrix.Norms.L2Operator

namespace IsotropicSpin

/-- **The norms `‖ZZ†‖ = ‖YY†‖ = 1`**, Alicki, arXiv:quant-ph/0402080v1, §2, proof of Theorem 1,
p. 3 (after (21)): "Because ZZ† is a positive matrix with trace equal 2 than it follows that its
norm ‖ZZ†‖ = ‖YY†‖ = 1".

1. `‖Z Z†‖ = 1` for all real `α, β`, with `Z` of (19);
2. `‖Y Y†‖ = 1` for every unit vector `ξ ∈ ℂ³`, with `Y = Σ_k ξ_k S_k` of (18).

**Formalization Note** `‖·‖` is the operator norm induced by the Euclidean norm
(`Matrix.Norms.L2Operator`). -/
theorem norm_ZZ_YY :
    (∀ α β : ℝ, ‖zMat α β * (zMat α β)ᴴ‖ = 1) ∧
    (∀ ξ : Fin 3 → ℂ, WHAdditivity.Renyi.IsUnitVector ξ → ‖yMat ξ * (yMat ξ)ᴴ‖ = 1) := by sorry

end IsotropicSpin
