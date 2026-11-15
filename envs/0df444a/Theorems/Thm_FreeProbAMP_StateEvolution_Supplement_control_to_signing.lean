-- Prove2me | Theorems.Thm_FreeProbAMP_StateEvolution_Supplement_control_to_signing
-- name    : FreeProbAMP.StateEvolution.Supplement.control_to_signing
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T05:57:43.706983+00:00
-- url     : https://prove2.me/theorems/88499b99-aa9a-4360-83ea-85d4fbb59855
-- title:
--   Theorem 3.2 — efficient signings from an admissible Brownian control
-- statement:
--   Let $(B_t)_{t\ge0}$ be a standard Brownian motion on a probability space $(\Omega,\mathcal F,\mathbb P)$ with completed natural filtration $\mathbb F$. Let $T\ge0$ and let $b=(b_t)_{t\ge0}$ be an $\mathbb F$-predictable control with
--
--   1. $b_s\ge0$ almost surely for every $s$, and $\int_0^T\mathbb E[b_s^2]\,ds<\infty$ (condition (3.1));
--   2. the Itô integral $G_t=\int_0^t b_s\,dB_s$ satisfies $G_T\in\{-1,+1\}$ almost surely (condition (3.2)).
--
--   For $\alpha>0$ let $J_\alpha(b)=\int_0^T\big(\sqrt{\mathbb E[b_s^2]}-\sqrt\alpha\,\mathbb E[b_s]\big)^2ds$.
--
--   Let $A_1,\dots,A_n$ be independent $d\times d$ GOE matrices (off-diagonal variance $1/d$, diagonal variance $2/d$), with $A(x)=n^{-1/2}\sum_i x_iA_i$ for $x\in\mathbb R^n$ and $A^*$ its normalized adjoint. Then for every $\varepsilon>0$ there is an efficient algorithm that accesses the matrices only through calls to $A$ and $A^*$, makes at most a constant number $N$ of such calls with $N$ independent of $d$, and outputs $\hat x\in\{-1,+1\}^n$ such that, whenever $2n/d^2\to\alpha$,
--
--   $$\mathbb P\big(\|A(\hat x)\|_{\mathrm{op}}\le 2\sqrt{J_\alpha(b)}+\varepsilon\big)\longrightarrow1\qquad(d\to\infty).$$
--
--   The theorem converts any admissible continuous-time control into a signing algorithm whose spectral norm is governed by the control cost $J_\alpha$; Theorem 3.3 and the heat-equation control of §3.4 are obtained by evaluating $J_\alpha$ on explicit controls.
--
--   **Formalization Note.** "Efficient algorithm" is an `OracleProgram`: one finite straight-line program, fixed before $n$ and $d$, over exact real arithmetic, whose instructions are constants, the dimensions $n,d$, fixed measurable scalar maps applied to scalars or coordinatewise to vectors, empirical means, linear combinations, calls $x\mapsto A(x)$ and $M\mapsto A^*(M)$, and a final coordinatewise sign with $\mathrm{sign}(0)=+1$. Its operation count is bounded by $K(n+1)(d+1)^2$ and its number of oracle calls is a constant. The program may depend on $\alpha$, $\varepsilon$ and the fixed control $b$. The Itô integral is the published `You2015.Shared.IsItoIntegral` relation, the filtration is the published `ABPOnline.brownFiltration`, and Brownian motion is Mathlib's `IsBrownianReal`.
--
--   Differences from the source:
--   - encoding: matrices A_1,…,A_n i.i.d. GOE(d) with 2n/d² → α, probability P over the matrices → any probability space (Ω′, μ), any n : ℕ → ℕ with 2n(d)/d² → α, and for each d a jointly independent family A d with each A_i of law GOE(d) (base GOEArray); the event's probability is μ of the event; reason: every GOE sequence in the source's regime is an instance and conversely; d ranges over all natural numbers, finitely many small d do not affect the limit
--   - reading: an efficient algorithm which linearly queries A and its adjoint A* → a deterministic OracleProgram: one fixed finite straight-line program, the same for every n and d, over exact real arithmetic, which touches A_1,…,A_n only through calls x ↦ A(x) and M ↦ A*(M) and applies fixed finite-arity measurable scalar maps coordinatewise at unit cost per coordinate; its operation count is at most K(n+1)(d+1)² with K independent of n, d; reason: the source fixes no computational model; this class contains the incremental AMP algorithm of §3.2–3.3 (constants, n and d, coordinatewise smooth maps and their derivatives, empirical averages, linear combinations, calls to A and A*, final rounding), and every member is efficient, so the existential claim is at least as strong as the source's
--   - reading: the number of calls to A and A* is bounded by a constant N = N(α, ε) independent of d → there is N with prog.queryCount ≤ N, where the program (hence N) is chosen after α, ε and the control b but before the sequence n(·), the probability space and the dimension d; reason: the source fixes b before the algorithm and its notation N(α, ε) suppresses this fixed design data; a straight-line program makes the same number of calls on every input
--   - encoding: sign vector x̂ = sign(·) ∈ {−1,+1}^n → coordinatewise sign with sign(0) = +1; reason: the output must lie in {−1,+1}^n; the convention at 0 is the one fixed in the brief and does not restrict the algorithm class
--   - encoding: standard Brownian motion (B_t) on (Ω, F, P) with its completed natural filtration → any probability space (Ω, P) and a process B with IsBrownianReal B P (Mathlib: Brownian finite-dimensional laws, a.s. continuous paths); the filtration is σ(B_s : s ≤ t) augmented by the P-null sets of the ambient σ-algebra (published ABPOnline.brownFiltration); reason: standard Brownian motion is exactly this; augmentation inside the ambient σ-algebra coincides with the completion on a complete space, and the completion of any space is again an instance
--   - encoding: G_t = ∫_0^t b_s dB_s (Itô integral) with G_T ∈ {−1,+1} a.s. → some process G is an Itô integral of b_s 1_{s ≤ T} in the sense of the published You2015.Shared.IsItoIntegral (L² limit of simple adapted integrals) and G_T ∈ {−1,+1} a.s.; reason: by Itô's isometry the L² construction determines G_T almost surely; truncating the integrand at T changes nothing on [0, T]
--   - encoding: J_α(b) = ∫_0^T (√(E b_s²) − √α E b_s)² ds → the same integrand integrated as a lower Lebesgue integral over s ∈ [0, T] and converted to a real number; reason: the integrand is nonnegative and its integral is finite for every control satisfying (3.1); the values agree
--   - encoding: b_s ≥ 0 a.s. in (3.1), for the times on which the control is defined → b_s ≥ 0 a.s. for every s ≥ 0, including s > T; reason: only b on [0, T] enters (3.2) and (3.3), and b·1_{[0,T]} is predictable, nonnegative for every s and has the same G_T and J_α(b), so no instance of the source is lost
-- source:
--   August Chen, Ahmed El Alaoui, STOC 2027 submission #1182 (October 2026), p. 7, Theorem 3.2, (3.4), with (3.1)–(3.3) on pp. 6–7; proof pp. 9–15

import Mathlib
import Definitions.Def_FreeProbAMP_StateEvolution_Matrices
import Definitions.Def_FreeProbAMP_StateEvolution_Supplement_Control
import Definitions.Def_FreeProbAMP_StateEvolution_Supplement_Oracle

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology
set_option autoImplicit false
noncomputable section

namespace FreeProbAMP.StateEvolution.Supplement

open FreeProbAMP.StateEvolution

/-- Theorem 3.2, submission p. 7: from an admissible Brownian control to efficient signings. -/
theorem control_to_signing
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (hB : IsBrownianReal B P)
    (T : ℝ≥0) (b : ℝ≥0 → Ω → ℝ) (hb : AdmissibleControl P B T b)
    (α : ℝ) (hα : 0 < α) (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∃ prog : OracleProgram,
      prog.queryCount ≤ N ∧
      (∃ K : ℕ, ∀ n d : ℕ, prog.cost n d ≤ K * (n + 1) * (d + 1) ^ 2) ∧
      ∀ {Ω' : Type*} [MeasurableSpace Ω'] (μ : Measure Ω') [IsProbabilityMeasure μ]
        (n : ℕ → ℕ) (A : (d : ℕ) → Ω' → Fin (n d) → RMat d),
        Tendsto (fun d => aspect (n d) d) atTop (𝓝 α) →
        (∀ d, GOEArray μ (A d)) →
        Tendsto (fun d => μ {ω | opNorm (applyA (A d ω) (prog.signing (A d ω)))
            ≤ 2 * Real.sqrt (controlCost P α T b) + ε}) atTop (𝓝 1) := by sorry

end FreeProbAMP.StateEvolution.Supplement
