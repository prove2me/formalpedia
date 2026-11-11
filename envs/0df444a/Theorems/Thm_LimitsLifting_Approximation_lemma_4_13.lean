-- Prove2me | Theorems.Thm_LimitsLifting_Approximation_lemma_4_13
-- name    : LimitsLifting.Approximation.lemma_4_13
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T04:39:10.525094+00:00
-- url     : https://prove2.me/theorems/a318563c-05fb-4149-9fe3-4d1a6b5cbe4b
-- title:
--   Lemma 4.13 — structured rectangles are $\rho$-like, and so is some row $\{x\}\times Y$
-- statement:
--   For every sufficiently large real $\Delta$ there is $n_0$ such that for all $n\ge n_0$ and $m\ge n^\Delta$ the following holds. If $R=X\times Y\subseteq[m]^n\times\{0,1\}^{mn}$ is $\rho$-structured, then $R$ is $\rho$-like, i.e.
--   $$G(X\times Y)=\{z\in\{0,1\}^n: z\text{ is consistent with }\rho\},$$
--   and further there is $x\in X$ such that $\{x\}\times Y$ is $\rho$-like.
--
--   The lemma lets the Prover in the simulation of Lemma 4.10 realize every answer consistent with its memory by a point of the current rectangle.
--
--   Differences from the source:
--   - encoding: if m ≥ n^Δ, for the large enough constant Δ of §4.2 → real Δ ≥ Δ₀ and integer m with (n : ℝ)^Δ ≤ (m : ℝ); reason: preserves all admissible real exponents; block length is an integer, with no rounding or restriction to integer exponents.
--   - encoding: [m], [n] → Fin m, Fin n; reason: index shift, same instances.
-- source:
--   Gaia Carenini, Bruno Cavalar, Stefan Grosser, Jan Pich, Limits of Lifting, STOC 2027 submission #309 (October 2026), Lemma 4.13 (citing [GGKS20, Lemma 4.4]), printed p. 23 (PDF p. 24)

import Mathlib
import Definitions.Def_MultiplierAssoc206_Resolution_CNF
import Definitions.Def_LimitsLifting_Approximation_ApproxModel
import Definitions.Def_LimitsLifting_Approximation_CanonicalCover
import Definitions.Def_LimitsLifting_Approximation_RectangleScheme
open MultiplierAssoc206.Resolution

namespace LimitsLifting.Approximation

theorem lemma_4_13 :
    ∃ Δ₀ : ℝ, ∀ Δ : ℝ, Δ₀ ≤ Δ → ∃ n₀ : ℕ, ∀ n m : ℕ, n₀ ≤ n → (n : ℝ) ^ Δ ≤ (m : ℝ) →
      ∀ (ρ : Restriction (Fin n)) (X : Finset (AliceIn n m)) (Y : Finset (BobIn n m)),
        IsStructured ρ X Y → IsLike ρ X Y ∧ ∃ x ∈ X, IsLike ρ {x} Y := by sorry

end LimitsLifting.Approximation
