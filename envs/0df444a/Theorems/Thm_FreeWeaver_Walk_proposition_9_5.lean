-- Prove2me | Theorems.Thm_FreeWeaver_Walk_proposition_9_5
-- name    : FreeWeaver.Walk.proposition_9_5
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T23:38:04.130202+00:00
-- url     : https://prove2.me/theorems/3693a877-9740-4df3-b149-d21afada069b
-- title:
--   Proposition 9.5 — the walk stops within n/min{t_o², t_*²} + 1 passes and returns signs with discrepancy < 57.3√ε
-- statement:
--   Let $v_1,\dots,v_n\in\mathbb C^m$ be nonzero with $\sum_iv_iv_i^*=I_m$, $m\ge1$, $\varepsilon=\max_i\|v_i\|^2$. Algorithm 2, with oracle answers within the tolerances of Proposition E.4, stops after at most $n/\min\{t_o^2,t_*^2\}+1$ passes through its loop; the invariant (9.2) holds throughout with total charge at most $\frac{101}{100}n\varepsilon\rho$; and the returned signs satisfy
--   $$\Big\|\sum_i\sigma_iA_i\Big\|<\Big(5\sqrt{128}+\tfrac{101}{10000}\Big)\Big(1+\tfrac12\sqrt{5/8192}\Big)\sqrt\varepsilon<57.3\sqrt\varepsilon .$$
--
--   Differences from the source:
--   - encoding: a standard free semicircular family in a C*-probability space (A, τ), represented on H with τ(a) = ⟨ω, aω⟩; ℂ^D ⊗ H → IsStdFreeSemicircular s ω on a complex Hilbert space H (unit ω, self-adjoint s_γ with the semicircle moments, freeness of the polynomial algebras of the s_γ, τ tracial and faithful on the generated C*-algebra); operators on ℂ^D ⊗ H as CStarMatrix ι ι (H →L[ℂ] H), D = card ι ≥ 1; id ⊗ τ as the matrix of ⟨ω, T_kl ω⟩; λ₊ = sSup of the real spectrum; reason: the paper's own realization (p. 13); faithfulness makes the spectrum and norm those of the abstract C*-algebra, so no instance changes
--   - encoding: ℂ^D with D = 2m, block-diagonal matrices with m × m blocks; the index set [n] × {0,1,2,3} → matrices indexed by Fin 2 × Fin m (I₂ ⊗ A is 1 ⊗ₖ A), the family indexed by Fin n × Fin 4, vectors indexed by Fin n from 0; reason: relabelling of the same coordinates
--   - encoding: the standing choices of §9: ε = max_i a_i, u = 128, the parameters (9.1), the smooth profile c_ζ with ζ = t_o/1000 → epsMax v, the literal 128, rho, tOut, zeta, eta, kappa, walkProfile n = smoothProfile 128 (zeta n); reason: the same quantities written out
--   - generalization: Algorithm 2 with the oracles of Appendix E.2 (Algorithm 3 and the procedure of Lemma E.8) → every oracle answer within the tolerances of Proposition E.4: q̂ with |q̂_i − q_i| ≤ η/(12u) and |𝔪̂ − 𝔪| ≤ 1/128, any unit h supported on the live set with xᵀh = 0 and ℱ''[h,h] < −κ/2, values of ℱ(x ± t_*h, z) to error κt_*²/96; reason: the paper says these tolerances are the only properties of the oracles used (p. 35); Algorithm 3's answers satisfy them (Proposition E.4), so the statement specializes to the paper's walk
--   - encoding: stops after at most n/min{t_o², t_*²} + 1 passes → every configuration reached after k passes has k ≤ n/min{t_o², t_*²}, and every reached configuration has a next pass; reason: a run that has not stopped after k passes makes at least k + 1 passes, and a pass is always possible, so every run returns within the bound
-- source:
--   Kathuria, A Walk From Free Probability to Matrix Discrepancy II, arXiv:2609.18913 (version dated November 3, 2026; sha256 c06bf728…), p. 36, Proposition 9.5

import Mathlib
import Definitions.Def_FreeWeaver_Walk_Pencil
import Definitions.Def_FreeWeaver_Walk_Weaver
import Definitions.Def_FreeWeaver_Walk_FreeModel
import Definitions.Def_FreeWeaver_Walk_Walk

open scoped ComplexOrder

namespace FreeWeaver.Walk

/-- Kathuria, *A Walk From Free Probability to Matrix Discrepancy II*, arXiv:2609.18913 (version
dated November 3, 2026; sha256 c06bf728…), p. 36, Proposition 9.5 (The walk): "Algorithm 2, with the oracles of Appendix E.2, stops
after at most n/min{to^2, t∗^2} + 1 passes through the loop. The invariant (9.2) holds throughout,
with total charge at most (101/100) n ε ρ, and the returned signs satisfy
∥Σ_i σi Ai∥ < (5√128 + 101/10000)(1 + (1/2)√(5/8192)) √ε < 57.3√ε."
Algorithm 2 is `WalkPass`, one pass of its loop with every oracle answer within the tolerances of
Proposition E.4; `WalkReach k cf` says some run is at the configuration `cf` after `k` passes.
Conclusions: a run that has not stopped after `k` passes has `k ≤ n/min{t_o², t_*²}` (so every run
stops within `n/min{t_o², t_*²} + 1` passes); every such configuration has a next pass; (9.2) holds
at every configuration with total charge at most `(101/100) n ε ρ`; returned signs satisfy the
bound. Standing assumptions of §9. -/
theorem proposition_9_5 {n m : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (hm : 1 ≤ m) (v : Fin n → Fin m → ℂ) (hv0 : ∀ i, v i ≠ 0)
    (hP : IsParseval v) (s : Fin n × Fin 4 → H →L[ℂ] H) (ω : H)
    (hs : IsStdFreeSemicircular s ω) :
    let ε := epsMax v
    let bound : ℝ := (5 * Real.sqrt 128 + 101 / 10000) * (1 + 1 / 2 * Real.sqrt (5 / 8192))
    (∀ (k : ℕ) (cf : WalkConf n), WalkReach v s ω k cf →
      (k : ℝ) ≤ (n : ℝ) / min (tOut n ^ 2) (tStar n m ε ^ 2)) ∧
    (∀ (k : ℕ) (cf : WalkConf n), WalkReach v s ω k cf → ∃ out, WalkPass v s ω cf out) ∧
    (∀ (k : ℕ) (cf : WalkConf n), WalkReach v s ω k cf →
      Inv92 (walkProfile n) v s ω ε cf.1 cf.2.1 cf.2.2 ∧
        cf.2.2 ≤ 101 / 100 * (n : ℝ) * ε * rho n) ∧
    (∀ (k : ℕ) (cf : WalkConf n) (σ : Fin n → ℝ), WalkReach v s ω k cf →
      WalkPass v s ω cf (Sum.inr σ) →
        IsSigns σ ∧ opNorm (signedSum v σ) < bound * Real.sqrt ε) ∧
    bound * Real.sqrt ε < 57.3 * Real.sqrt ε := by sorry

end FreeWeaver.Walk
