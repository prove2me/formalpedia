-- Prove2me | Theorems.Thm_FreeProbAMP_StateEvolution_Supplement_three_stage_control
-- name    : FreeProbAMP.StateEvolution.Supplement.three_stage_control
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T05:58:12.676907+00:00
-- url     : https://prove2.me/theorems/6c9fc0cd-90b2-49b3-9f55-3c009a7e9fbc
-- title:
--   Theorem 3.3 — three-stage control and $O(1/\sqrt{\alpha\log\alpha})$ signings for $\alpha>32/(3\pi^2)$
-- statement:
--   Let $\alpha_0=32/(3\pi^2)$. For $\eta>0$ let $f_\eta(z)=c_\eta/(\eta+1-z^2)^2$ on $[-1,1]$ (zero elsewhere), with $c_\eta$ the normalizing constant, let $Z_\eta\sim f_\eta$, and set
--
--   $$v_\eta=\mathbb E[Z_\eta^2],\qquad h_\eta=2\,\mathbb E\Big[\varphi\Big(\Phi^{-1}\Big(\tfrac{1+Z_\eta}{2}\Big)\Big)\Big],$$
--
--   where $\varphi$ and $\Phi$ are the standard normal density and distribution function. Controls $b$, the conditions (3.1)–(3.2) and the cost $J_\alpha(b)$ are as in Theorem 3.2. The theorem asserts:
--
--   1. For every $\alpha>\alpha_0$ there exist $\eta=\eta_\alpha>0$ and a control $b$ satisfying (3.1)–(3.2) with
--   $$J_\alpha(b)\le1-v_\eta+\alpha h_\eta^2 .$$
--   2. The choice $\alpha\mapsto\eta_\alpha$ can be made so that $\eta_\alpha\to0$ as $\alpha\to\infty$ and
--   $$1-v_{\eta_\alpha}+\alpha h_{\eta_\alpha}^2=O\Big(\frac{1}{\alpha\log\alpha}\Big)\qquad(\alpha\to\infty).$$
--   3. Consequently there are constants $C,\alpha_1>0$ such that for every $\alpha>\alpha_1$ an efficient algorithm (in the sense of Theorem 3.2) outputs a signing $\hat x\in\{-1,+1\}^n$ with, whenever $2n/d^2\to\alpha$ and $A_1,\dots,A_n$ are independent GOE matrices,
--   $$\mathbb P\Big(\|A(\hat x)\|_{\mathrm{op}}\ge\frac{C}{\sqrt{\alpha\log\alpha}}\Big)\longrightarrow0\qquad(d\to\infty).$$
--
--   This is the large-aspect-ratio consequence of the general control-to-signing theorem: an explicit three-stage control drives the achievable operator norm to $O(1/\sqrt{\alpha\log\alpha})$.
--
--   **Formalization Note.** In Lean, items 1 and 2 are one selection function $\eta_\alpha$ that works in item 1 for every $\alpha>\alpha_0$, for every standard Brownian motion on every probability space. The big-O is Mathlib's `IsBigO` along `atTop`. The quantile $\Phi^{-1}(p)$ is the least $x$ with $p\le\Phi(x)$ for $0<p<1$ and is set to $0$ at the Lebesgue-null endpoints. Algorithms are `OracleProgram`s as in Theorem 3.2.
--
--   Differences from the source:
--   - reading: for every α > α_0 there exists η = η_α > 0 …; moreover, η can be selected so that η_α → 0 as α → ∞, and 1 − v_η + α h_η² = O(1/(α log α)) → one function α ↦ η_α which is positive and feasible for the cost bound at every α > α_0, tends to 0 as α → ∞, and satisfies the big-O bound as α → ∞ (Mathlib IsBigO along atTop); reason: the stronger of the two readings; the selection is the same η of the first clause (the proof of Lemma 3.10, p. 20, picks the smallest solution for every α > α_0)
--   - reading: there exists … a control b satisfying (3.1)–(3.2) such that J_α(b) ≤ 1 − v_η + α h_η² → for every standard Brownian motion on every probability space there are a horizon T ≥ 0 and a control b satisfying (3.1)–(3.2) with J_α(b) ≤ 1 − v_{η_α} + α h_{η_α}²; reason: (3.1)–(3.2) refer to the Brownian motion fixed on p. 6, whatever it is; quantifying over every Brownian motion covers it; the horizon is part of (3.1)
--   - encoding: Z_η ∼ f_η, v_η = E Z_η², h_η = 2 E φ(Φ^{-1}((1+Z_η)/2)) → expectations are integrals against the density f_η (zero outside [−1,1]); Φ^{-1}(p) is the least x with p ≤ Φ(x) for 0 < p < 1 and 0 for p ∉ (0,1); reason: the values p = 0, 1 occur only at z = ±1, a Lebesgue-null set; nothing else changes
--   - reading: one can efficiently obtain a signing x̂ ∈ {−1,+1}^n such that P(∥A(x̂)∥_op ≥ C/√(α log α)) → 0 → for each α > α_1 there is a deterministic OracleProgram (as in Theorem 3.2) whose output satisfies the displayed limit in the regime 2n/d² → α; reason: same computational reading as in Theorem 3.2, whose algorithm the source invokes
--   - encoding: sign vector x̂ = sign(·) ∈ {−1,+1}^n → coordinatewise sign with sign(0) = +1; reason: the output must lie in {−1,+1}^n; the convention at 0 is the one fixed in the brief and does not restrict the algorithm class
--   - encoding: matrices A_1,…,A_n i.i.d. GOE(d) with 2n/d² → α, probability P over the matrices → any probability space (Ω′, μ), any n : ℕ → ℕ with 2n(d)/d² → α, and for each d a jointly independent family A d with each A_i of law GOE(d) (base GOEArray); the event's probability is μ of the event; reason: every GOE sequence in the source's regime is an instance and conversely; d ranges over all natural numbers, finitely many small d do not affect the limit
--   - encoding: standard Brownian motion (B_t) on (Ω, F, P) with its completed natural filtration → any probability space (Ω, P) and a process B with IsBrownianReal B P (Mathlib: Brownian finite-dimensional laws, a.s. continuous paths); the filtration is σ(B_s : s ≤ t) augmented by the P-null sets of the ambient σ-algebra (published ABPOnline.brownFiltration); reason: standard Brownian motion is exactly this; augmentation inside the ambient σ-algebra coincides with the completion on a complete space, and the completion of any space is again an instance
--   - encoding: G_t = ∫_0^t b_s dB_s (Itô integral) with G_T ∈ {−1,+1} a.s. → some process G is an Itô integral of b_s 1_{s ≤ T} in the sense of the published You2015.Shared.IsItoIntegral (L² limit of simple adapted integrals) and G_T ∈ {−1,+1} a.s.; reason: by Itô's isometry the L² construction determines G_T almost surely; truncating the integrand at T changes nothing on [0, T]
--   - encoding: J_α(b) = ∫_0^T (√(E b_s²) − √α E b_s)² ds → the same integrand integrated as a lower Lebesgue integral over s ∈ [0, T] and converted to a real number; reason: the integrand is nonnegative and its integral is finite for every control satisfying (3.1); the values agree
--   - encoding: b_s ≥ 0 a.s. in (3.1), for the times on which the control is defined → b_s ≥ 0 a.s. for every s ≥ 0, including s > T; reason: only b on [0, T] enters (3.2) and (3.3), and b·1_{[0,T]} is predictable, nonnegative for every s and has the same G_T and J_α(b), so no instance of the source is lost
-- source:
--   August Chen, Ahmed El Alaoui, STOC 2027 submission #1182 (October 2026), p. 8, Theorem 3.3, (3.6)–(3.8); proof pp. 16–20

import Mathlib
import Definitions.Def_FreeProbAMP_StateEvolution_Matrices
import Definitions.Def_FreeProbAMP_StateEvolution_Supplement_Control
import Definitions.Def_FreeProbAMP_StateEvolution_Supplement_Density
import Definitions.Def_FreeProbAMP_StateEvolution_Supplement_Oracle

open MeasureTheory ProbabilityTheory Filter Asymptotics
open scoped NNReal ENNReal Topology
set_option autoImplicit false
noncomputable section

namespace FreeProbAMP.StateEvolution.Supplement

open FreeProbAMP.StateEvolution

/-- Theorem 3.3, submission p. 8: the three-stage control for `α > 32/(3π²)`, its cost bound,
the `O(1/(α log α))` asymptotics, and the resulting efficient signings. -/
theorem three_stage_control :
    (∃ ηsel : ℝ → ℝ,
      (∀ α : ℝ, alpha0 < α → 0 < ηsel α ∧
        ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
          (B : ℝ≥0 → Ω → ℝ), IsBrownianReal B P →
          ∃ (T : ℝ≥0) (b : ℝ≥0 → Ω → ℝ), AdmissibleControl P B T b ∧
            controlCost P α T b ≤ 1 - secondMoment (ηsel α) + α * hCoeff (ηsel α) ^ 2) ∧
      Tendsto ηsel atTop (𝓝 0) ∧
      (fun α : ℝ => 1 - secondMoment (ηsel α) + α * hCoeff (ηsel α) ^ 2)
        =O[atTop] (fun α : ℝ => 1 / (α * Real.log α))) ∧
    ∃ C α₁ : ℝ, 0 < C ∧ 0 < α₁ ∧ ∀ α : ℝ, α₁ < α →
      ∃ prog : OracleProgram,
        (∃ K : ℕ, ∀ n d : ℕ, prog.cost n d ≤ K * (n + 1) * (d + 1) ^ 2) ∧
        ∀ {Ω' : Type*} [MeasurableSpace Ω'] (μ : Measure Ω') [IsProbabilityMeasure μ]
          (n : ℕ → ℕ) (A : (d : ℕ) → Ω' → Fin (n d) → RMat d),
          Tendsto (fun d => aspect (n d) d) atTop (𝓝 α) →
          (∀ d, GOEArray μ (A d)) →
          Tendsto (fun d => μ {ω | C / Real.sqrt (α * Real.log α)
              ≤ opNorm (applyA (A d ω) (prog.signing (A d ω)))}) atTop (𝓝 0) := by sorry

end FreeProbAMP.StateEvolution.Supplement
