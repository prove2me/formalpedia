-- Prove2me | Theorems.Thm_GMMPostSamp_Main_proposition_4
-- name    : GMMPostSamp.Main.proposition_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T06:28:51.548024+00:00
-- url     : https://prove2.me/theorems/be5af22d-1e2b-406b-bda6-76ce51df6a0a
-- title:
--   Proposition 4 — LearnGMM recovers θ⋆ up to relabelling within r, the relabelled 3r-balls are disjoint, in time O(nd² + nk³)
-- statement:
--   There are an admissible program LearnGMM and a universal constant $C>0$ such that for all $k,d,n\ge1$, $\sigma>0$, $0<a\le A$, $\alpha\in[a,A]^k$ and $\delta,r\in(0,\frac16)$, with $\tau=\frac1{Ak}(\frac\delta{8k})^{1/a}$: if $d\ge C(k+\log\frac1\delta)$ and $n\ge C\frac{d^3k^{11}(1+\sigma^8)}{\tau^6r^2}$, then LearnGMM, given $(k,d,n,\delta,x_{[n]})$, halts within $C(nd^2+nk^3)+C$ steps on every run, and outside an event of probability at most $\delta$ over Model 1 and its tapes it returns $\bar\theta\in\Theta$ with
--   $$\min_{\theta'\in\mathrm{Orb}(\bar\theta)}\|\theta'-\theta^\star\|_2\le r\quad\text{and}\quad\Phi_c(B)\cap\Phi_{c'}(B)=\emptyset\ \ (c\ne c'),\qquad B=\{\theta\in\Theta:\|\theta-\bar\theta\|_2\le3r\}.$$
--   It is the estimator used for preconditioning (§3.1).
--
--   **Formalization Note.** The machine has no eigensolver (see finding I1 on the paper's Algorithm 3). The success event's complement is measured under (Model 1) $\otimes$ (tape law).
--
--   Differences from the source:
--   - reading: δ, r ∈ (0, 1/6)² → δ ∈ (0, 1/6) and r ∈ (0, 1/6); reason: the pair (δ, r) lies in (0, 1/6)²
--   - reading: d = Ω(k + log 1/δ), n = Ω(d³k¹¹(1+σ⁸)/(τ⁶r²)), runtime O(nd² + nk³), 'for appropriate constants' → one universal C: d ≥ C(k + log(1/δ)), n ≥ C·d³k¹¹(1+σ⁸)/(τ⁶r²), every run within C(nd² + nk³) + C steps; reason: explicit universal constants for each Ω(·)/O(·)
--   - encoding: algorithm LearnGMM (Algorithm 3) taking x_[n] (and k, δ) → an admissible program on the machine of §2.1 with input (k, d, n, δ, x_[n]); θ̄ decoded from the output cells; reason: §2.1's real RAM; the input sizes d, n are part of the input layout
--   - encoding: an event E of probability ≥ 1 − δ over Model 1 and Algorithm 3, under which … → the (outer) measure under Model 1 ⊗ tapes of the set where the run does not return θ̄ ∈ Θ with both properties is ≤ δ; reason: equivalent formulation of 'there is such an event'
--   - encoding: min over Orb(θ̄) of ‖θ′ − θ⋆‖₂ ≤ r → ∃ c ∈ S_k with ‖Φ_c(θ̄) − θ⋆‖₂ ≤ r; reason: the orbit is finite
-- source:
--   Kumar, Sarkar, Tian, Zhu, Posterior Sampling in Gaussian Mixture Models Beyond the Clusterability Threshold, STOC 2027 submission (manuscript sha256 ba5079cd…), p. 18, Proposition 4 (Theorem 3 of [HK13]); proof pp. 43–45

import Mathlib
import Definitions.Def_SmaleNinth_RealRAM
import Definitions.Def_PolyVoting_dirichletMeasure
import Definitions.Def_GMMPostSamp_Main_Toolkit
import Definitions.Def_GMMPostSamp_Main_Model
import Definitions.Def_GMMPostSamp_Main_Machine

open MeasureTheory ProbabilityTheory

namespace GMMPostSamp.Main

/-- Proposition 4 (p. 18; [HK13, Theorem 3]): there are a program LearnGMM and a universal `C`
such that for `δ, r ∈ (0, 1/6)`, `d ≥ C(k + log(1/δ))` and `n ≥ C d³k¹¹(1 + σ⁸)/(τ⁶r²)`,
`τ = (1/(Ak))(δ/(8k))^{1/a}`, LearnGMM on `(k, d, n, δ, x_[n])` halts within
`C(nd² + nk³) + C` steps on every run, and outside an event of probability at most `δ` over
Model 1 and the program's tapes it returns `θ̄ ∈ Θ` with `min_{θ' ∈ Orb(θ̄)} ‖θ' − θ⋆‖₂ ≤ r`
and `Φ_c(B) ∩ Φ_{c'}(B) = ∅` for all `c ≠ c'`, `B = {θ ∈ Θ : ‖θ − θ̄‖₂ ≤ 3r}`. -/
theorem proposition_4 : ∃ L : Machine.Program, Machine.Admissible L ∧ ∃ C : ℝ, 0 < C ∧
    ∀ k d n : ℕ, 1 ≤ k → 1 ≤ d → 1 ≤ n → ∀ (σ a A δ r : ℝ) (α : Fin k → ℝ),
      0 < σ → 0 < a → a ≤ A → (∀ i, α i ∈ Set.Icc a A) →
      0 < δ → δ < 1 / 6 → 0 < r → r < 1 / 6 →
      let τ : ℝ := (1 / (A * k)) * (δ / (8 * k)) ^ (1 / a)
      C * ((k : ℝ) + Real.log (1 / δ)) ≤ d →
      C * ((d : ℝ) ^ 3 * (k : ℝ) ^ 11 * (1 + σ ^ 8) / (τ ^ 6 * r ^ 2)) ≤ n →
      (∀ x : Fin n → E d, Machine.HaltsWithin L
          ([(k : ℝ), (d : ℝ), (n : ℝ), δ] ++ Machine.dataCells x)
          (C * (n * (d : ℝ) ^ 2 + n * (k : ℝ) ^ 3) + C)) ∧
      ((joint k d n σ α).prod Machine.tapeLaw) {q | ¬ ∃ θbar : Param k d,
          (Machine.finalState L Machine.noOracle
              ([(k : ℝ), (d : ℝ), (n : ℝ), δ] ++ Machine.dataCells q.1.2.2) q.2).map
              (Machine.decodeParam k d) = some θbar ∧
            θbar ∈ Theta k d ∧ OrbitClose θbar q.1.1 r ∧ OrbitDisjoint θbar (3 * r)}
        ≤ ENNReal.ofReal δ := by sorry

end GMMPostSamp.Main
