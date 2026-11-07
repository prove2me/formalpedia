-- Prove2me | Theorems.Thm_LiftSAParity_eq_26_pivot_bound
-- name    : LiftSAParity.eq_26_pivot_bound
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T13:11:07.685591+00:00
-- url     : https://prove2.me/theorems/e8ac2ca9-45b1-45e3-8ab6-ab3d5e983b18
-- title:
--   Eq. (26) — $\mu_J(A)\le 2^{-|I^\star(J,A)|}$
-- statement:
--   Let $\mathcal D$ be a $d$-local distribution for a CNF formula $F$ on $n$ variables, $\gamma$ any family of inputs $\gamma_{j,b}\in\{0,1\}^\ell$, $J\in[\ell]^n$, and $A\subseteq\mathbb F_2^{n\times\ell}$ a nonempty affine space. Then
--   $$\mu_J(A)\le 2^{-|I^\star(J,A)|},$$
--   where $I^\star(J,A)$ is the set of pivot blocks of the block-selection procedure.
--
--   Given all variables except the stifled variables $y_{i,J_i}$ of the pivot blocks, the equations of $A$ determine those variables uniquely, and they are sampled uniformly and independently; this is the first step of item (4).
--
--   **Formalization Note** $\mu_J$ is `muJ d D γ J`, $I^\star$ is `pivots d J A`.
--
--   Differences from the source:
--   - generalization: stated for A with rk A = r under the standing hypotheses of §4 (ℓ ≥ 2, d ≥ 4ℓ, F unsatisfiable, g 1-stifling with stifling inputs γ) → every nonempty affine A, every ℓ, d and every γ; only D d-local for F; reason: the argument uses none of the dropped hypotheses; the Lean statement specializes to the printed one
--   - generalization: integers n ≥ 1 (§2, p.7) → n : ℕ, including n = 0; reason: at n = 0 the cube has a single point and the statement is degenerate; the Lean statement specializes to the printed one for n ≥ 1
-- source:
--   de Rezende, Engström, Shekhovtsov, Lifting Sherali-Adams Degree to Unary Sherali-Adams over Parities Size (manuscript, sha256 cab5a032…), §4.2, p.14, eq. (26)

import Mathlib
import Definitions.Def_LiftSAParity_CNF
import Definitions.Def_LiftSAParity_IsLocalDist
import Definitions.Def_LiftSAParity_IsStiflingInputs
import Definitions.Def_LiftSAParity_lift
import Definitions.Def_LiftSAParity_IsAffineSpace
import Definitions.Def_LiftSAParity_blocks
import Definitions.Def_LiftSAParity_mu

namespace LiftSAParity

/-- **Eq. (26)** (de Rezende–Engström–Shekhovtsov, *Lifting Sherali-Adams Degree to Unary Sherali-Adams over
Parities Size*, manuscript (sha256 cab5a032…), §4.2, p.14): the pivot bound. "Conditional on all the values to all
variables except y_{i,J_i}'s for i ∈ I⋆(J, A), the defining equations of A have a unique solution
(if any) for y_{i,J_i}s. Since the value for these variables are sampled uniformly and
independently, we have that µ_J(A) ≤ 2^{−|I⋆(J,A)|}."

For every family `D` that is a `d`-local distribution for `F`, every choice of inputs `γ`, every
`J ∈ [ℓ]^n` and every nonempty affine space `A ⊆ 𝔽₂^{n×ℓ}`, `µ_J(A) ≤ 2^{−|I⋆(J,A)|}`.

**Formalization Note** The printed context is `rk A = r` under the standing hypotheses of §4;
the bound is stated for every nonempty affine `A`, every `γ`, `ℓ` and `d`. -/
theorem eq_26_pivot_bound {n ℓ d : ℕ} (F : CNF (Fin n)) (D : (I : Finset (Fin n)) → (I → Bool) → ℝ)
    (hD : IsLocalDist F d D) (γ : Fin ℓ → Bool → (Fin ℓ → Bool)) (J : Fin n → Fin ℓ)
    (A : Set (Fin n × Fin ℓ → ZMod 2)) (hA : IsAffineSpace A) (hne : A.Nonempty) :
    muJ d D γ J A ≤ (1 / 2 : ℝ) ^ (pivots d J A).card := by sorry

end LiftSAParity
