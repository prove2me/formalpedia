-- Prove2me | Theorems.Thm_MatMulPolyBarrier_Operational_values_5_5
-- name    : MatMulPolyBarrier.Operational.values_5_5
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T04:08:24.192227+00:00
-- url     : https://prove2.me/theorems/bf8c3743-1eff-4fb5-922d-059f2e247ca0
-- title:
--   §5.5 — $F^\star_\theta(\langle r\rangle)=r$ and $F^\star_\theta(\langle n_1,n_2,n_3\rangle)=n_1^{p_2}n_2^{p_3}n_3^{p_1}$
-- statement:
--   Let $\theta\in\Theta$. For every positive integer $n$, Definition 5.5 gives
--   $$F^\star_\theta(1,n,n)=\bigl(\theta_3+(1-\theta_3)A_3\bigr)^{p_1}=n^{p_1},\qquad F^\star_\theta(n,1,n)=n^{p_2},\qquad F^\star_\theta(n,n,1)=n^{p_3},$$
--   where $A_3=(n-\theta_3)/(1-\theta_3)$ is computed at the triple $(1,n,n)$. In particular $F^\star_\theta(\langle1\rangle)=F^\star_\theta(1,1,1)=1$, so $F^\star_\theta(\langle r\rangle)=r$ for every positive integer $r$, and, $F^\star_\theta$ being multiplicative,
--   $$F^\star_\theta(\langle n_1,n_2,n_3\rangle)=n_1^{p_2}\,n_2^{p_3}\,n_3^{p_1}$$
--   for all positive integers $n_1,n_2,n_3$.
--
--   Differences from the source:
--   - encoding: indices 1, 2, 3 of θ, p and A → 0, 1, 2; positive integers n, r, n₁, n₂, n₃ → naturals with hypotheses ≥ 1; ⟨r⟩, ⟨n₁, n₂, n₃⟩ → unitR r, mm n₁ n₂ n₃ (fixed bracketings); reason: Lean indexing and the shorthands of the definition file; same instances
-- source:
--   Amanov, van den Berg, Zuiddam, Multiplying matrices via polynomials: operational asymptotic spectrum barrier, STOC 2027 submission (manuscript sha256 38bd5183…), p. 39, §5.5, proof of Proposition 5.7 (values at ⟨r⟩ and ⟨n1, n2, n3⟩)

import Mathlib
import Definitions.Def_MatMulPolyBarrier_Operational_FExpr
import Definitions.Def_MatMulPolyBarrier_Operational_Fstar

set_option autoImplicit false

namespace MatMulPolyBarrier.Operational

/-- §5.5, proof of Proposition 5.7, p. 39: for `θ ∈ Θ` and positive integers `n`, `r`, `n₁, n₂, n₃`:
`F⋆_θ(1, n, n) = (θ₃ + (1 − θ₃)A₃)^{p₁} = n^{p₁}`, `F⋆_θ(n, 1, n) = n^{p₂}`, `F⋆_θ(n, n, 1) = n^{p₃}`;
`F⋆_θ(⟨1⟩) = F⋆_θ(1, 1, 1) = 1`, `F⋆_θ(⟨r⟩) = r`, and
`F⋆_θ(⟨n₁, n₂, n₃⟩) = n₁^{p₂} n₂^{p₃} n₃^{p₁}`. -/
theorem values_5_5 (θ : Fin 3 → ℝ) (hθ : InTheta θ) :
    (∀ n : ℕ, 1 ≤ n →
      FstarTriple θ ![1, (n : ℝ), (n : ℝ)] =
          (θ 2 + (1 - θ 2) * Acoord θ ![1, (n : ℝ), (n : ℝ)] 2) ^ pExp θ 0 ∧
        (θ 2 + (1 - θ 2) * Acoord θ ![1, (n : ℝ), (n : ℝ)] 2) ^ pExp θ 0 = (n : ℝ) ^ pExp θ 0 ∧
        FstarTriple θ ![(n : ℝ), 1, (n : ℝ)] = (n : ℝ) ^ pExp θ 1 ∧
        FstarTriple θ ![(n : ℝ), (n : ℝ), 1] = (n : ℝ) ^ pExp θ 2) ∧
    Fstar θ unitOne = FstarTriple θ ![1, 1, 1] ∧ FstarTriple θ ![1, 1, 1] = 1 ∧
    (∀ r : ℕ, 1 ≤ r → Fstar θ (unitR r) = r) ∧
    (∀ n₁ n₂ n₃ : ℕ, 1 ≤ n₁ → 1 ≤ n₂ → 1 ≤ n₃ →
      Fstar θ (mm n₁ n₂ n₃) =
        (n₁ : ℝ) ^ pExp θ 1 * (n₂ : ℝ) ^ pExp θ 2 * (n₃ : ℝ) ^ pExp θ 0) := by sorry

end MatMulPolyBarrier.Operational
