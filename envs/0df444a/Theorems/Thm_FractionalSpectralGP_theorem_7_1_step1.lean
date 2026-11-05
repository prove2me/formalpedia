-- Prove2me | Theorems.Thm_FractionalSpectralGP_theorem_7_1_step1
-- name    : FractionalSpectralGP.theorem_7_1_step1
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:27:41.683161+00:00
-- url     : https://prove2.me/theorems/eb5531c0-86e2-48a5-af1b-a340d67161c0
-- title:
--   Theorem 7.1, STEP 1 — a strongly continuous $Y:[a,b]\to S_{-1}$ is uniformly continuous into one $\mathcal H'_p$
-- statement:
--   Let $a,b\in\mathbb R$ and let $Y:[a,b]\to S_{-1}$ be continuous in the strong topology of $S_{-1}$. Then there exists $p\in\mathbb N$, $p\ge1$, such that $Y(t)\in\mathcal H'_p$ for all $t\in[a,b]$, and $Y$ is uniformly continuous from $[a,b]$ into $\mathcal H'_p$.
--
--   This reduces the Kondratiev-valued integrand to a single Hilbert space, where Våge's inequality applies.
--
--   Differences from the source:
--   - encoding: formal series Σ f_α H_α and the norm ‖·‖_k of H′_k → coefficient families ℓ → ℂ and the ℓ²-norm of (f_α (2ℕ)^{−kα/2}); reason: the defining isometry of H′_k; same objects
--   - encoding: multi-indices α = (α_1, α_2, …) with weight 2k at coordinate k → α : ℕ →₀ ℕ, coordinate n carries Z_n and weight 2(n + 1); reason: index shift k = n + 1; same objects
--   - encoding: continuous in the strong topology of S_{−1} → uniform convergence of ⟨Y(s) − Y(t), g⟩ → 0 on bounded subsets of S₁, at every t ∈ [a, b]; reason: the strong dual topology of S_{−1} = S₁', which for this DFS space is the inductive limit topology
--   - encoding: p ∈ ℕ (the paper's ℕ = {1, 2, …}) → p : ℕ with 1 ≤ p; reason: the paper writes ℕ₀ for {0, 1, …}
-- source:
--   Alpay, Jorgensen, Levanony, A class of Gaussian processes with fractional spectral measures, arXiv:1009.0233v1, Theorem 7.1, STEP 1, p.25 (proved in [1], STEP 2 of the proof of Theorem 5.1)

import Mathlib
import Definitions.Def_FractionalSpectralGP_MemHprime
import Definitions.Def_FractionalSpectralGP_embedHprime
import Definitions.Def_FractionalSpectralGP_MemSminus1
import Definitions.Def_FractionalSpectralGP_IsStronglyContinuousOn

open MeasureTheory Complex Filter Topology ProbabilityTheory
open scoped SchwartzMap ENNReal

namespace FractionalSpectralGP

/-- Theorem 7.1, STEP 1 (Alpay, Jorgensen, Levanony, arXiv:1009.0233v1, p.25; proved in [1], STEP 2 of the proof of
Theorem 5.1): if `Y : [a, b] → S_{−1}` is continuous in the strong topology of `S_{−1}`, there
exists `p ∈ ℕ` such that `Y(t) ∈ 𝓗'_p` for all `t ∈ [a, b]` and `Y` is uniformly continuous from
`[a, b]` into `𝓗'_p`.

**Formalization Note.** `ℕ = {1, 2, …}` in the paper, so `1 ≤ p`. `𝓗'_p` carries its Hilbert norm
through the isometry `embedHprime p`. -/
theorem theorem_7_1_step1 (a b : ℝ) (Y : ℝ → (ℕ →₀ ℕ) → ℂ)
    (hY : ∀ t ∈ Set.Icc a b, MemSminus1 (Y t)) (hYc : IsStronglyContinuousOn Y a b) :
    ∃ p : ℕ, 1 ≤ p ∧ (∀ t ∈ Set.Icc a b, MemHprime p (Y t)) ∧
      UniformContinuousOn (fun t => embedHprime p (Y t)) (Set.Icc a b) := by sorry

end FractionalSpectralGP
