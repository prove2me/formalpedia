-- Prove2me | Theorems.Thm_GMMPostSamp_Main_lemma_8
-- name    : GMMPostSamp.Main.lemma_8
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T06:29:03.07998+00:00
-- url     : https://prove2.me/theorems/37dca57f-423b-4ea7-a4c5-f04b207ac712
-- title:
--   Lemma 8 — the permutation oracle O_θ: c | θ is a weighted perfect-matching law, sampled within ξ in time O(k⁴ log⁷(k/ξ))
-- statement:
--   There are an admissible program and a universal $C>0$ such that for all $k,d\ge1$, $0<a\le A$, $\alpha\in[a,A]^k$, every $\theta=(w,\mu)\in\Theta$ with all $w_i>0$ and every $\xi\in(0,\frac12)$: the program, given $(k,d,\xi,\alpha,\theta)$, halts within $C\,k^4\log^7(k/\xi)+C$ steps on every run and outputs $c\in S_k$ whose law satisfies
--   $$\mathrm{TV}\Big(\mathrm{Law}(c),\ \tilde\Pi_B(\cdot\mid\theta)\Big)\le\xi,\qquad\tilde\Pi_B(c\mid\theta)=\frac{\prod_iw_i^{\alpha_{c(i)}-1}}{Z_\alpha(w)}.$$
--   It implements the oracle $O_\theta$ of Definition 1 required by Corollary 1.
--
--   **Formalization Note.** The output permutation is decoded from $k$ cells holding $c(i)+1$; anything else counts as `none`.
--
--   Differences from the source:
--   - generalization: on the event E of Lemma 7, for any θ ∈ B → for every θ ∈ Θ with all w_i > 0 (the program sees only k, d, ξ, α, θ); reason: on E every θ ∈ B has w_i ≥ τ/2 > 0, so the statement specializes to the paper's
--   - reading: an algorithm that implements a ξ-conditional sampling oracle O_θ in time O(k⁴ log⁷(k/ξ)) → an admissible program on the machine, every run within C k⁴ log⁷(k/ξ) + C steps, output law within ξ of (32); reason: §2.1's real RAM; explicit universal constant
-- source:
--   Kumar, Sarkar, Tian, Zhu, Posterior Sampling in Gaussian Mixture Models Beyond the Clusterability Threshold, STOC 2027 submission (manuscript sha256 ba5079cd…), p. 23, Lemma 8

import Mathlib
import Definitions.Def_SmaleNinth_RealRAM
import Definitions.Def_PolyVoting_dirichletMeasure
import Definitions.Def_GMMPostSamp_Main_Toolkit
import Definitions.Def_GMMPostSamp_Main_Model
import Definitions.Def_GMMPostSamp_Main_Machine

open MeasureTheory ProbabilityTheory

namespace GMMPostSamp.Main

/-- Lemma 8 (p. 23): there is a program that, given `(k, d, ξ, α, θ)` with `θ ∈ Θ`, all
`w_i > 0` and `ξ ∈ (0, 1/2)`, halts within `C k⁴ log⁷(k/ξ) + C` steps on every run and outputs
`c ∈ S_k` with law within `ξ` in TV of `Π̃_B(c | θ) ∝ ∏_i w_i^{α_{c(i)} − 1}` (32): a
`ξ`-conditional sampling oracle `O_θ`. -/
theorem lemma_8 : ∃ P : Machine.Program, Machine.Admissible P ∧ ∃ C : ℝ, 0 < C ∧
    ∀ k d : ℕ, 1 ≤ k → 1 ≤ d → ∀ (a A ξ : ℝ) (α : Fin k → ℝ) (θ : Param k d),
      0 < a → a ≤ A → (∀ i, α i ∈ Set.Icc a A) → θ ∈ Theta k d → (∀ i, 0 < θ.1 i) →
      0 < ξ → ξ < 1 / 2 →
      Machine.HaltsWithin P ([(k : ℝ), (d : ℝ), ξ] ++ List.ofFn α ++ Machine.paramCells θ)
          (C * (k : ℝ) ^ 4 * Real.log (k / ξ) ^ 7 + C) ∧
      tvFin (fun o : Option (Equiv.Perm (Fin k)) => (Machine.tapeLaw {τ |
            (Machine.finalState P Machine.noOracle
              ([(k : ℝ), (d : ℝ), ξ] ++ List.ofFn α ++ Machine.paramCells θ) τ).bind
              (Machine.decodePerm k) = o}).toReal)
          (fun o => match o with
            | none => 0
            | some c => condPermMass α θ.1 c) ≤ ξ := by sorry

end GMMPostSamp.Main
