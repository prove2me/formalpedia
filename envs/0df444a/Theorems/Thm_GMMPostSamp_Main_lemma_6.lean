-- Prove2me | Theorems.Thm_GMMPostSamp_Main_lemma_6
-- name    : GMMPostSamp.Main.lemma_6
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T06:25:52.241458+00:00
-- url     : https://prove2.me/theorems/8a7d618b-7a19-4a74-8347-f245bc3b0af4
-- title:
--   Lemma 6 — ξ-conditional sampling oracles move the output of Algorithm 1 by at most 2Tξ in TV
-- statement:
--   In Model 1 ($\sigma>0$, $\alpha\in[a,A]^k$), fix inputs $(x_{[n]},\bar\theta,r,T)$ to Algorithm 1 with $\bar\theta\in\Theta$, $r>0$, and let $\xi\in(0,\frac12)$. Let $(\theta,c)$ be the output of Algorithm 1 with the exact conditional draws $\tilde\Pi_B(\cdot\mid c_t)$ (line 4) and $\tilde\Pi_B(\cdot\mid\theta_{t+1})$ (line 5), and $(\tilde\theta,\tilde c)$ the output when lines 4 and 5 are implemented with $\xi$-conditional sampling oracles $(O_c,O_\theta)$ for $\tilde\Pi_B$. Then
--   $$\mathrm{TV}\big(\mathrm{Law}(\theta,c),\mathrm{Law}(\tilde\theta,\tilde c)\big)\le2T\xi.$$
--   It lets Corollary 1 use approximate conditional samplers.
--
--   **Formalization Note.** The exact $c\mid\theta$ draw is any Markov kernel equal to (32) at every $\theta\in B$ with all $w_i>0$ (the draws $\theta_{t+1}$ lie there almost surely).
--
--   Differences from the source:
--   - reading: Lines 4 and 5 in Algorithm 3 → lines 4 and 5 of Algorithm 1 (the two conditional draws); reason: typo: Algorithm 3 is LearnGMM; the lemma fixes inputs to Algorithm 1 (finding I2)
--   - encoding: exact draws and oracles in Algorithm 1 → Markov kernels; the exact c | θ kernel equals (32) on B ∩ {all w_i > 0}; θ_0 := θ̄; reason: (32) is defined for positive weights, the boundary is Π̃_B-null; θ_0 is never used for T ≥ 1
--   - reading: ξ-conditional sampling oracles (Definition 1): for all θ ∈ B → for all θ ∈ B with all w_i > 0; reason: (32) is undefined at w_i = 0 when α_{c(i)} < 1; such θ form a Π̃_B-null set
--   - reading: fix inputs (x_[n], θ̄, r, T) to Algorithm 1 → θ̄ ∈ Θ, r > 0, T ∈ ℕ, in Model 1's setting (σ > 0, α ∈ [a, A]^k, k, d, n ≥ 1); reason: the input specification of Algorithm 1
-- source:
--   Kumar, Sarkar, Tian, Zhu, Posterior Sampling in Gaussian Mixture Models Beyond the Clusterability Threshold, STOC 2027 submission (manuscript sha256 ba5079cd…), p. 21, Lemma 6

import Mathlib
import Definitions.Def_PolyVoting_dirichletMeasure
import Definitions.Def_GMMPostSamp_Main_Toolkit
import Definitions.Def_GMMPostSamp_Main_Model

open MeasureTheory ProbabilityTheory

namespace GMMPostSamp.Main

/-- Lemma 6 (p. 21): for fixed inputs `(x_[n], θ̄, r, T)` to Algorithm 1 and `ξ ∈ (0, 1/2)`,
replacing the exact conditional draws of lines 4 and 5 by `ξ`-conditional sampling oracles for
`Π̃_B` moves the law of the output `(θ_T, c_T)` by at most `2Tξ` in total variation. -/
theorem lemma_6 {k d n : ℕ} (hk : 1 ≤ k) (hd : 1 ≤ d) (hn : 1 ≤ n) (σ a A : ℝ)
    (α : Fin k → ℝ) (hσ : 0 < σ) (ha : 0 < a) (haA : a ≤ A) (hα : ∀ i, α i ∈ Set.Icc a A)
    (x : Fin n → E d) (θbar : Param k d) (hθbar : θbar ∈ Theta k d) (r : ℝ) (hr : 0 < r)
    (T : ℕ) (ξ : ℝ) (hξ0 : 0 < ξ) (hξ1 : ξ < 1 / 2)
    (Kexact : Kernel (Param k d) (Equiv.Perm (Fin k))) [IsMarkovKernel Kexact]
    (hKexact : ∀ θ ∈ ballB θbar (3 * r), (∀ i, 0 < θ.1 i) → Kexact θ = condPerm α θ.1)
    (Kθ : Kernel (Param k d) (Equiv.Perm (Fin k))) [IsMarkovKernel Kθ]
    (Kc : Kernel (Equiv.Perm (Fin k)) (Param k d)) [IsMarkovKernel Kc]
    (horacles : IsCondOracles σ α x θbar (3 * r) ξ Kθ Kc) :
    tv (alg1Law (exactParamKernel σ α x θbar (3 * r)) Kexact θbar T) (alg1Law Kc Kθ θbar T)
      ≤ 2 * T * ξ := by sorry

end GMMPostSamp.Main
