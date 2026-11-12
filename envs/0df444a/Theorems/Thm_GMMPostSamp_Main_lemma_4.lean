-- Prove2me | Theorems.Thm_GMMPostSamp_Main_lemma_4
-- name    : GMMPostSamp.Main.lemma_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T06:28:40.344382+00:00
-- url     : https://prove2.me/theorems/87578216-857a-4266-8448-0bc1c21b632a
-- title:
--   Lemma 4 — labels drawn from (27) at a δ-accurate parameter draw are δ-accurate for the label posterior, in time O(ndk)
-- statement:
--   In Model 1 ($k,d,n\ge1$, $\sigma>0$, $\alpha\in[a,A]^k$, $0<a\le A$), there are an admissible program $Q$ and a universal constant $C>0$ such that for every $x_{[n]}$:
--   $Q$, given $(k,d,n,\sigma,\alpha,x_{[n]},\theta)$, halts within $C\,ndk+C$ steps on every run for every $\theta\in\Theta$; and for every $\delta$ and every probability law $\rho$ of $\theta$ with $\mathrm{TV}(\rho,\Pi)\le\delta$ ($\Pi$ the parameter posterior (26)), the labels $\iota_{[n]}$ output by $Q$ on $\theta\sim\rho$ satisfy
--   $$\mathrm{TV}\big(\mathrm{Law}(\iota_{[n]}),\pi\big)\le\delta,$$
--   $\pi$ the label posterior (24). It reduces sampling labels to sampling parameters.
--
--   **Formalization Note.** $\mathrm{Law}(\iota_{[n]})$ is the law under $\rho\otimes$ tapes of the decoded output on $[k]^n\cup\{\text{none}\}$; "none" (no halt or invalid output) has posterior mass $0$.
--
--   Differences from the source:
--   - reading: we can compute ι_[n] in time O(ndk) → a program Q on the machine (k, d, n, σ, α, x, θ as input) halting within C·ndk + C steps on every run for every θ ∈ Θ, C universal; reason: §2.1's real RAM; each O(·) is an explicit universal constant
--   - encoding: θ with TV(Law(θ), Π) ≤ δ → any probability measure ρ on (Fin k → ℝ) × (Fin k → ℝ^d) with tv ρ Π ≤ δ; output law under ρ ⊗ tapes; reason: Law(θ) is a probability measure on parameters
--   - encoding: ι_[n] ∈ [k]^n → output on Option (Fin n → Fin k), none counted against TV; reason: a run that does not halt or writes an invalid label is not a valid output
-- source:
--   Kumar, Sarkar, Tian, Zhu, Posterior Sampling in Gaussian Mixture Models Beyond the Clusterability Threshold, STOC 2027 submission (manuscript sha256 ba5079cd…), p. 17, Lemma 4

import Mathlib
import Definitions.Def_SmaleNinth_RealRAM
import Definitions.Def_PolyVoting_dirichletMeasure
import Definitions.Def_GMMPostSamp_Main_Toolkit
import Definitions.Def_GMMPostSamp_Main_Model
import Definitions.Def_GMMPostSamp_Main_Machine

open MeasureTheory ProbabilityTheory

namespace GMMPostSamp.Main

/-- Lemma 4 (p. 17): there is a program that, on `(k, d, n, σ, α, x_[n], θ)`, outputs labels
`ι_[n]` in `C·ndk + C` steps on every run and every `θ ∈ Θ`, such that whenever `θ` is drawn
from a law within `δ` of the parameter posterior `Π` in TV, the labels are within `δ` of the
label posterior `π`. -/
theorem lemma_4 : ∃ Q : Machine.Program, Machine.Admissible Q ∧ ∃ C : ℝ, 0 < C ∧
    ∀ k d n : ℕ, 1 ≤ k → 1 ≤ d → 1 ≤ n → ∀ (σ a A δ : ℝ) (α : Fin k → ℝ) (x : Fin n → E d),
      0 < σ → 0 < a → a ≤ A → (∀ i, α i ∈ Set.Icc a A) →
      (∀ θ ∈ Theta k d, Machine.HaltsWithin Q
          ([(k : ℝ), (d : ℝ), (n : ℝ), σ] ++ List.ofFn α ++ Machine.dataCells x ++
            Machine.paramCells θ) (C * n * d * k + C)) ∧
      ∀ ρ : Measure (Param k d), IsProbabilityMeasure ρ → tv ρ (paramPost σ α x) ≤ δ →
        Machine.tvLabels (fun o => ((ρ.prod Machine.tapeLaw) {p |
            (Machine.finalState Q Machine.noOracle
              ([(k : ℝ), (d : ℝ), (n : ℝ), σ] ++ List.ofFn α ++ Machine.dataCells x ++
                Machine.paramCells p.1) p.2).bind (Machine.decodeLabels k n) = o}).toReal)
          (labelPost σ α x) ≤ δ := by sorry

end GMMPostSamp.Main
