-- Prove2me | Theorems.Thm_OnDemandCoord_theorem_1
-- name    : OnDemandCoord.theorem_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:22:10.997397+00:00
-- url     : https://prove2.me/theorems/fa4396f4-ff44-429a-a040-004a4f928511
-- title:
--   Theorem 1 (corrected: no atoms of the total demand): system-wide optimal staffing
-- statement:
--   **Theorem 1 (System-wide Optimality)**, p. 12. Let $Q^p$ satisfy $p\bar F_i(Q^p_i)=c$ for all $i$ and $\varphi^p=p\,\mathbb P(X_i>Q^p_i\text{ for some }i)$, and $\varphi(x)=x+G(x)/g(x)$.
--
--   1. If $\underline\tau\ge\varphi^p$, then $(Q^p,\underline\tau)$ is a system optimum: only permanent workers are used.
--   2. Suppose $\sum_iX_i$ has no atom on $(0,\infty)$ and $p\,\mathbb P(\sum_iX_i>N)<\bar\tau+1/g(\bar\tau)$. Then equation (6), $$\mathbb P\Big(\sum_iX_i>NG(\eta)\Big)=\frac1p\Big(\eta+\frac{G(\eta)}{g(\eta)}\Big),$$ has exactly one solution $\eta^o$ in $(\underline\tau,\bar\tau)$. Let $\varphi^o=\varphi(\eta^o)$. If $c\ge\varphi^o$, then $(0,\eta^o)$ is a system optimum: only on-demand workers are used.
--   3. Under the hypotheses of 2, if $\underline\tau<\varphi^p$ and $c<\varphi^o$, a system optimum exists, and every system optimum $(Q^*,\eta^*)$ uses both workforces ($S^*=NG(\eta^*)>0$ and $Q^*\ne0$), and if $\mathbb P(\sum_i(X_i-Q^*_i)^+=S^*)=0$ it satisfies
--   $$p\,\mathbb P\Big(S^*<\sum_i(X_i-Q^*_i)^+\Big)=\eta^*+\frac{G(\eta^*)}{g(\eta^*)},\qquad p\,\mathbb P\Big(Q^*_i<X_i,\ S^*<\sum_j(X_j-Q^*_j)^+\Big)=c\quad\forall i .$$
--
--   The theorem describes the centralized benchmark that the contracts of §5 must reproduce.
--
--   Differences from the source:
--   - encoding: the model of §3 (continuous nonnegative demands with finite mean, any joint law; G continuous, log-concave, with density g > 0 on [τ̲, τ̄]) → OnDemandCoord.Model: X_i measurable, integrable, ≥ 0 a.s., atomless law; G continuous, monotone, 0 left of τ̲, 1 right of τ̄, G′ = g > 0 within [τ̲, τ̄], log G concave on (τ̲, τ̄]; reason: readings of the standing assumptions, stated once on the definition; no instance of the paper is excluded
--   - correction: (ii)–(iii) for any joint law of X → no atom of ΣX_i on (0, ∞) in (ii)–(iii), and P(Σ(X_i − Q_i*)⁺ = S*) = 0 for the two equalities of (iii); reason: §3 leaves the joint law free; with X_2 = 1 − X_1, X_1 ~ U(0,1), p = 3, c = 2, G uniform on [0.5, 1.5], N = 10, (6) has no solution and the optimum (Q* = 0, S* = 1) violates (iii)'s first equality (paper.md item 2)
--   - reading: N sufficiently large (footnote 16) → p·P(ΣX_i > N) < τ̄ + 1/g(τ̄); reason: the weakest condition under which (6) has a solution in (τ̲, τ̄); it holds for all large N
--   - reading: η* = τ̲, Q* = Q^p (resp. Q* = 0, η* = η°) is optimal → (Q^p, τ̲) (resp. (0, η°)) is a global minimizer of (5); reason: 'it is optimal to' read as optimality; minimizers need not be unique
--   - encoding: Q^p_i = F_i⁻¹(p − c/p) → any Q^p with p·F̄_i(Q^p_i) = c; reason: the printed formula means F_i⁻¹((p − c)/p); the solution may be non-unique and φ^p does not depend on the choice
--   - reading: 'Otherwise' in (iii) → τ̲ < φ^p and c < φ°; reason: the negation of the hypotheses of (i) and (ii)
--   - reading: ∀ i ∈ I in (iii) → every firm, including those with Q_i* = 0; reason: at an optimum with Q* ≠ 0 the equality holds also where Q_i* = 0
-- source:
--   Lu–Zheng–Zhong, Maximizing the Benefits of an On-Demand Workforce: Fill Rate-Based Allocation and Coordination Mechanisms, SSRN:2783617 (PDF of 2023-05-13; article doi:10.1287/msom.2021.0327), Theorem 1, p. 12; (6) and footnote 16, p. 12; proof §A.1, pp. A1–A2 (PDF 33–34)

import Mathlib
import Definitions.Def_OnDemandCoord_Coordinates

namespace OnDemandCoord

open MeasureTheory ProbabilityTheory

/-- **Theorem 1 (System-wide Optimality), corrected**, Lu–Zheng–Zhong, SSRN:2783617 (PDF of 2023-05-13), p. 12.

Clause (i): if `φ^p ≤ τl`, then `(Q^p, τl)` is a system optimum. Clauses (ii)–(iii): when `ΣX_i` has
no atom on `(0, ∞)` and `p P(ΣX_i > N) < τu + 1/g(τu)`, equation (6) has a unique solution `η°` in
`(τl, τu)`; if `c ≥ φ° = φ(η°)`, then `(0, η°)` is a system optimum; if `τl < φ^p` and `c < φ°`, a system
optimum exists and every system optimum uses both workforces, and it satisfies the two displayed optimality conditions when
`P(Σ_i (X_i − Q_i)⁺ = S) = 0`.

**Formalization Note.** `Q^p` is any solution of `p F̄_i = c`. The no-atom hypotheses are a correction:
§3 leaves the joint law free, and a sum with atoms has no solution of (6). The bound on
`P(ΣX_i > N)` pins down "`N` sufficiently large" of footnote 16. -/
theorem theorem_1 {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {n : ℕ} (M : Model Ω P n)
    (Qp : Fin n → ℝ) (hQp : M.IsPermanentBenchmark Qp) :
    (M.phiP Qp ≤ M.τl → M.IsSystemOptimum Qp M.τl) ∧
    ((∀ x : ℝ, 0 < x → P {ω | ∑ i, M.X i ω = x} = 0) →
      M.p * M.tailSum M.N < M.τu + 1 / M.g M.τu →
      ∃ ηo ∈ Set.Ioo M.τl M.τu,
        M.tailSum (M.S ηo) = M.phi ηo / M.p ∧
        (∀ η ∈ Set.Ioo M.τl M.τu, M.tailSum (M.S η) = M.phi η / M.p → η = ηo) ∧
        (M.phi ηo ≤ M.c → M.IsSystemOptimum 0 ηo) ∧
        (M.τl < M.phiP Qp → M.c < M.phi ηo →
          (∃ (Q : Fin n → ℝ) (η : ℝ), M.IsSystemOptimum Q η) ∧
          ∀ (Q : Fin n → ℝ) (η : ℝ), M.IsSystemOptimum Q η →
            0 < M.S η ∧ Q ≠ 0 ∧
            (P {ω | ∑ i, M.vac Q i ω = M.S η} = 0 →
              M.p * P.real {ω | M.S η < ∑ i, M.vac Q i ω} = η + M.G η / M.g η ∧
              ∀ i, M.p * P.real {ω | Q i < M.X i ω ∧ M.S η < ∑ i, M.vac Q i ω} = M.c))) := by sorry

end OnDemandCoord
