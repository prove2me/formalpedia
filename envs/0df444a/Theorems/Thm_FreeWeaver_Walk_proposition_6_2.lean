-- Prove2me | Theorems.Thm_FreeWeaver_Walk_proposition_6_2
-- name    : FreeWeaver.Walk.proposition_6_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T23:36:29.191835+00:00
-- url     : https://prove2.me/theorems/632fad0d-6924-41c9-b6e3-ac1504f5f35f
-- title:
--   Proposition 6.2 — exact second variation of the potential along a direction on the live coordinates
-- statement:
--   In the setting of §6 — a state $x\in[-1,1]^n$, $z>\lambda_+(\mathcal Y(x))$, at least one live coordinate, a profile $c$ infinitely differentiable at every live $x_i$, and $h\in\mathbb R^n$ vanishing off the live set — the second variation $\mathcal F''[h,h]=\frac{d^2}{dt^2}\mathcal F(x+th,z)|_{t=0}$ satisfies
--   $$D\,\mathcal F''[h,h]=4\operatorname{Tr}(Q\mathcal G_t^2)+2\langle\mathcal G_{st},\Lambda(\mathcal G_{st})\rangle+4\operatorname{Tr}(Q\Psi_1(\mathcal G_t))-4\operatorname{Tr}(P^2\mathcal G_t^2)-2\operatorname{Tr}(P\mathcal G_tP\mathcal G_t)+\sum_ic''(x_i)h_i^2(2q_ir_i+p_i^2),$$
--   and the two terms $-4\operatorname{Tr}(P^2\mathcal G_t^2)$ and $-2\operatorname{Tr}(P\mathcal G_tP\mathcal G_t)$ are nonpositive. It is the identity behind the curvature estimate of §7.
--
--   Differences from the source:
--   - encoding: a standard free semicircular family in a C*-probability space (A, τ), represented on H with τ(a) = ⟨ω, aω⟩; ℂ^D ⊗ H → IsStdFreeSemicircular s ω on a complex Hilbert space H (unit ω, self-adjoint s_γ with the semicircle moments, freeness of the polynomial algebras of the s_γ, τ tracial and faithful on the generated C*-algebra); operators on ℂ^D ⊗ H as CStarMatrix ι ι (H →L[ℂ] H), D = card ι ≥ 1; id ⊗ τ as the matrix of ⟨ω, T_kl ω⟩; λ₊ = sSup of the real spectrum; reason: the paper's own realization (p. 13); faithfulness makes the spectrum and norm those of the abstract C*-algebra, so no instance changes
--   - encoding: ℂ^D with D = 2m, block-diagonal matrices with m × m blocks; the index set [n] × {0,1,2,3} → matrices indexed by Fin 2 × Fin m (I₂ ⊗ A is 1 ⊗ₖ A), the family indexed by Fin n × Fin 4, vectors indexed by Fin n from 0; reason: relabelling of the same coordinates
--   - encoding: the identity (6.6) between real numbers; derivatives of matrix-valued maps; 'infinitely differentiable at x_i' → an identity in ℂ (the real D·ℱ'' cast), the nonpositivity as −4Tr(…) ≤ 0 in ℂ's order (real and nonpositive); entrywise derivatives; ContDiffAt ℝ ∞ c (x i); reason: same values; the traces are real for Hermitian arguments
-- source:
--   Kathuria, A Walk From Free Probability to Matrix Discrepancy II, arXiv:2609.18913 (version dated November 3, 2026; sha256 c06bf728…), p. 31, Proposition 6.2

import Mathlib
import Definitions.Def_FreeWeaver_Walk_Pencil
import Definitions.Def_FreeWeaver_Walk_Weaver
import Definitions.Def_FreeWeaver_Walk_FreeModel

open scoped ComplexOrder

namespace FreeWeaver.Walk

/-- Kathuria, *A Walk From Free Probability to Matrix Discrepancy II*, arXiv:2609.18913 (version
dated November 3, 2026; sha256 c06bf728…), p. 31, Proposition 6.2 (Exact second variation): "In the setting above, with
ℱ''[h, h] = d²/dt² ℱ(x + th, z)|_{t=0}, D · ℱ''[h, h] = 4 Tr(Q𝒢t^2) + 2⟨𝒢st, Λ(𝒢st)⟩
+ 4 Tr(QΨ1(𝒢t)) − 4 Tr(P^2 𝒢t^2) − 2 Tr(P𝒢t P𝒢t) + Σ_i c''(xi) hi^2 (2qi ri + pi^2). (6.6) The two
terms on the second line that contain 𝒢t are nonpositive."
The setting of §6 (p. 29): a state `x ∈ [−1, 1]^n`, `z > λ₊(Y(x))`, at least one live coordinate, a
profile `c` (Definition 4.1, `u = 128`) infinitely differentiable at every live `x_i`, a direction
`h` with `h_i = 0` off the live set; standing assumptions of §4.1 on `v`. -/
theorem proposition_6_2 {n m : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (hm : 1 ≤ m) (v : Fin n → Fin m → ℂ) (hv0 : ∀ i, v i ≠ 0)
    (hP : IsParseval v) (s : Fin n × Fin 4 → H →L[ℂ] H) (ω : H)
    (hs : IsStdFreeSemicircular s ω) (c : ℝ → ℝ) (hc : IsProfile 128 c)
    (x : Fin n → ℝ) (hx : ∀ i, |x i| ≤ 1) (z : ℝ) (hz : edge c v s x < z)
    (hk : ∃ i, |x i| < 1)
    (hsmooth : ∀ i, |x i| < 1 → ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) c (x i))
    (h : Fin n → ℝ) (hh : ∀ i, ¬ |x i| < 1 → h i = 0) :
    let P := balP c v s ω x z
    let Q := balQ c v s ω x z
    let Gt := respT c v s ω x z h
    let Gst := respST c v s ω x z h
    ((((2 * m : ℕ) : ℝ) * secondVar c v s ω x z h : ℝ) : ℂ) =
        4 * (Q * Gt ^ 2).trace + 2 * hsInner Gst (LamMap c v s ω x z Gst) +
          4 * (Q * Psi1Map c v s ω x z h Gt).trace -
          4 * (P ^ 2 * Gt ^ 2).trace - 2 * (P * Gt * P * Gt).trace +
          ((∑ i, deriv (deriv c) (x i) * h i ^ 2 *
            (2 * qCoef c v s ω x z i * rCoef c v s ω x z i + pCoef c v s ω x z i ^ 2) : ℝ) : ℂ) ∧
      -4 * (P ^ 2 * Gt ^ 2).trace ≤ 0 ∧ -2 * (P * Gt * P * Gt).trace ≤ 0 := by sorry

end FreeWeaver.Walk
