-- Prove2me | Theorems.Thm_FreeWeaver_Walk_lemma_9_3
-- name    : FreeWeaver.Walk.lemma_9_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T23:38:01.086566+00:00
-- url     : https://prove2.me/theorems/c87acbe5-3e85-4d85-a2b5-2ce2052efc7c
-- title:
--   Lemma 9.3 — outward tests: a passed test is an accepted move of length t_o at charge t_oηε; all tests failing gives (7.1) with L = 2/0.999²
-- statement:
--   In the setting of §9, let $z>\lambda_+(\mathcal Y(x))$, $\mathcal F(x,z)\le B$, $|x_i|<1-\rho$ for every live $i$, $\ell_i=(c(x_i)-c(x_i+\operatorname{sgn}(x_i)t_o))/t_o$, and $|\hat q_i-q_i|\le\eta/(12u)$ for live $i$. (a) If $\ell_i\hat q_i\ge1-\eta/2$, then $x'=x+\operatorname{sgn}(x_i)t_oe_i$, $z'=z+t_o\eta\varepsilon$ give $z'>\lambda_+(\mathcal Y(x'))$, $\mathcal F(x',z')\le\mathcal F(x,z)\le B$ and $\|x'\|_2^2\ge\|x\|_2^2+t_o^2$. (b) If $\ell_i\hat q_i<1-\eta/2$ for every live $i$, then (7.1) holds at $(x,z)$ with
--   $$L=2/0.999^2 .$$
--
--   Differences from the source:
--   - encoding: a standard free semicircular family in a C*-probability space (A, τ), represented on H with τ(a) = ⟨ω, aω⟩; ℂ^D ⊗ H → IsStdFreeSemicircular s ω on a complex Hilbert space H (unit ω, self-adjoint s_γ with the semicircle moments, freeness of the polynomial algebras of the s_γ, τ tracial and faithful on the generated C*-algebra); operators on ℂ^D ⊗ H as CStarMatrix ι ι (H →L[ℂ] H), D = card ι ≥ 1; id ⊗ τ as the matrix of ⟨ω, T_kl ω⟩; λ₊ = sSup of the real spectrum; reason: the paper's own realization (p. 13); faithfulness makes the spectrum and norm those of the abstract C*-algebra, so no instance changes
--   - encoding: ℂ^D with D = 2m, block-diagonal matrices with m × m blocks; the index set [n] × {0,1,2,3} → matrices indexed by Fin 2 × Fin m (I₂ ⊗ A is 1 ⊗ₖ A), the family indexed by Fin n × Fin 4, vectors indexed by Fin n from 0; reason: relabelling of the same coordinates
--   - encoding: the standing choices of §9: ε = max_i a_i, u = 128, the parameters (9.1), the smooth profile c_ζ with ζ = t_o/1000 → epsMax v, the literal 128, rho, tOut, zeta, eta, kappa, walkProfile n = smoothProfile 128 (zeta n); reason: the same quantities written out
-- source:
--   Kathuria, A Walk From Free Probability to Matrix Discrepancy II, arXiv:2609.18913 (version dated November 3, 2026; sha256 c06bf728…), p. 36, Lemma 9.3

import Mathlib
import Definitions.Def_FreeWeaver_Walk_Pencil
import Definitions.Def_FreeWeaver_Walk_Weaver
import Definitions.Def_FreeWeaver_Walk_FreeModel
import Definitions.Def_FreeWeaver_Walk_Walk

open scoped ComplexOrder

namespace FreeWeaver.Walk

/-- Kathuria, *A Walk From Free Probability to Matrix Discrepancy II*, arXiv:2609.18913 (version
dated November 3, 2026; sha256 c06bf728…), p. 36, Lemma 9.3 (Outward tests): "Let z > λ+(Y(x)), let ℱ(x, z) ≤ B, and let
|xi| < 1 − ρ for every live i. For live i let ℓi = (c(xi) − c(xi + sgn(xi)to))/to. Let q̂i satisfy
|q̂i − qi| ≤ η/(12u). (a) If ℓi q̂i ≥ 1 − η/2, then the move x' = x + sgn(xi) to ei,
z' = z + to η ε gives z' > λ+(Y(x')) and ℱ(x', z') ≤ ℱ(x, z), so ℱ(x', z') ≤ B. Also
∥x'∥_2^2 ≥ ∥x∥_2^2 + to^2. (b) If ℓi q̂i < 1 − η/2 for every live i, then (7.1) holds at (x, z) with
L = 2/0.999^2."
Standing assumptions of §9 as in Lemma 9.1; `ℓ_i` is `secant n x i`. -/
theorem lemma_9_3 {n m : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (hm : 1 ≤ m) (v : Fin n → Fin m → ℂ) (hv0 : ∀ i, v i ≠ 0)
    (hP : IsParseval v) (s : Fin n × Fin 4 → H →L[ℂ] H) (ω : H)
    (hs : IsStdFreeSemicircular s ω) (x : Fin n → ℝ) (hx : ∀ i, |x i| ≤ 1) (z : ℝ)
    (hz : edge (walkProfile n) v s x < z)
    (hF : potential (walkProfile n) v s ω x z ≤ budget 128 (epsMax v))
    (hlive : ∀ i, |x i| < 1 → |x i| < 1 - rho n)
    (qhat : Fin n → ℝ)
    (hq : ∀ i, |x i| < 1 → |qhat i - qCoef (walkProfile n) v s ω x z i| ≤ eta n / (12 * 128)) :
    let ε := epsMax v
    let c := walkProfile n
    -- (a)
    (∀ i, |x i| < 1 → 1 - eta n / 2 ≤ secant n x i * qhat i →
      let x' := Function.update x i (x i + sgn (x i) * tOut n)
      let z' := z + tOut n * eta n * ε
      edge c v s x' < z' ∧ potential c v s ω x' z' ≤ potential c v s ω x z ∧
        potential c v s ω x' z' ≤ budget 128 ε ∧
        ∑ j, x j ^ 2 + tOut n ^ 2 ≤ ∑ j, x' j ^ 2) ∧
    -- (b)
    ((∀ i, |x i| < 1 → secant n x i * qhat i < 1 - eta n / 2) →
      Assumption71 c v s ω x z 128 (2 / (0.999 : ℝ) ^ 2)) := by sorry

end FreeWeaver.Walk
