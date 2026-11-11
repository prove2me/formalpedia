-- Prove2me | Theorems.Thm_OAI_DirectionalBallisticityUnfolded_exists_velocity_of_directionally_transient
-- name    : OAI.DirectionalBallisticityUnfolded.exists_velocity_of_directionally_transient
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T00:06:26.302845+00:00
-- url     : https://prove2.me/theorems/4e46b3bb-5112-47ad-a377-aebeca331223
-- title:
--   Directional transience implies ballisticity (unit direction), with the walk's definitions written out
-- statement:
--   A random walk in a random environment on $\mathbb Z^d$, $d \ge 2$, with nearest-neighbour steps. An environment assigns to each site $x$ a row $\omega(x)$, a probability vector $(\omega(x)_e)_e$ indexed by the $2d$ steps $e \in \{1,\dots,d\} \times \{\pm\}$ (entries in $\mathbb R_{\ge 0}$, summing to $1$); the rows are i.i.d. with law $\nu$, and $\nu$ is uniformly elliptic: there is $\kappa > 0$ with $\omega(x)_e \ge \kappa$ for $\nu$-almost every row and every step $e$. The walk starts at $0$ and, in environment $\omega$, steps from $x$ by $e$ with probability $\omega(x)_e$. Write $P$ for the annealed law of the path (the environment averaged out).
--
--   Let $\ell \in \mathbb R^d$ be a unit vector. If $\langle X_n, \ell\rangle \to \infty$ holds $P$-almost surely (directional transience), then there is $v \in \mathbb R^d$ with $\langle v, \ell \rangle > 0$ and $X_n / n \to v$ $P$-almost surely (ballisticity with an asymptotic velocity).
--
--   The walk is described without any definitions bundle: the transition kernel $K$ on the state (environment, position) is a Markov kernel given by the hypothesis `hK`, that is $K(\omega, x) = \sum_e \omega(x)_e\, \delta_{(\omega,\, x + e)}$, where the step $e$ is the unit vector of the coordinate in the given direction. The path law is `Kernel.trajMeasure` of $K$ started from the law of (environment, $0$) and projected to the position coordinate, as `hP` states.
--
--   This is the unit-direction theorem of the OpenAI development (`OAI.DirectionalTransience.directional_transience_implies_ballisticity`) with its definitions unfolded. It exists because the two published definitions bundles of that development declare the same names, so a proof using theorems stated in both needs a statement mentioning neither.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/DirectionalBallisticity.lean (the statement `OAI.DirectionalTransience.MainStatement`, with its definitions written out)

import Mathlib

open MeasureTheory ProbabilityTheory Filter in
open scoped ENNReal NNReal BigOperators Topology in
theorem OAI.DirectionalBallisticityUnfolded.exists_velocity_of_directionally_transient
    {d : ℕ} (hd : 2 ≤ d)
    (ν : Measure {p : (Fin d × Bool) → ℝ≥0 // ∑ e, p e = 1}) [IsProbabilityMeasure ν]
    (hue : ∃ κ : ℝ≥0, 0 < κ ∧ ∀ᵐ p ∂ν, ∀ e, κ ≤ p.1 e)
    (ℓ : Fin d → ℝ) (hℓ : ∑ i, ℓ i * ℓ i = 1)
    (K : Kernel (((Fin d → ℤ) → {p : (Fin d × Bool) → ℝ≥0 // ∑ e, p e = 1}) × (Fin d → ℤ))
      (((Fin d → ℤ) → {p : (Fin d × Bool) → ℝ≥0 // ∑ e, p e = 1}) × (Fin d → ℤ)))
    [IsMarkovKernel K]
    (hK : ∀ z, K z = ∑ e : Fin d × Bool,
      ((z.1 z.2).1 e : ℝ≥0∞) • Measure.dirac (z.1, z.2 +
        (fun i => if i = e.1 then (if e.2 then (1 : ℤ) else -1) else 0)))
    (P : Measure (ℕ → Fin d → ℤ))
    (hP : P = (@Kernel.trajMeasure
      (fun _ => ((Fin d → ℤ) → {p : (Fin d × Bool) → ℝ≥0 // ∑ e, p e = 1}) × (Fin d → ℤ)) _
      ((Measure.infinitePi (fun _ : (Fin d → ℤ) => ν)).map (fun ω => (ω, (0 : Fin d → ℤ))))
      (fun n => K.comap (fun z : ((i : Finset.Iic n) → _) => z ⟨n, Finset.mem_Iic.mpr le_rfl⟩)
        (measurable_pi_apply _)) _).map (fun z n => (z n).2))
    (htrans : ∀ᵐ X ∂P, Tendsto (fun n => ∑ i, (X n i : ℝ) * ℓ i) atTop atTop) :
    ∃ v : Fin d → ℝ, 0 < ∑ i, v i * ℓ i ∧
      ∀ᵐ X ∂P, Tendsto (fun n : ℕ => fun i => (X n i : ℝ) / (n : ℝ)) atTop (𝓝 v) := by
  sorry
