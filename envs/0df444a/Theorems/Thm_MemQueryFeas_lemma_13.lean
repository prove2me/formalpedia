-- Prove2me | Theorems.Thm_MemQueryFeas_lemma_13
-- name    : MemQueryFeas.lemma_13
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T02:39:26.455456+00:00
-- url     : https://prove2.me/theorems/6d114d4f-3a92-4182-9989-cad02a5cbcf4
-- title:
--   Lemma 13 — posterior density bound $p_{E^{(i)}\mid E^{(\le i-1)}}\le e^{d\tilde d(\delta^{(i-1)}+\dots+\delta^{(N)})\kappa(T)}\,p_{\mathrm{Unif}(B(E^{(i-1)},\delta^{(i-1)}))}$
-- statement:
--   Fix an invertible linear map $T$, accuracies $\delta^{(0)}\ge\dots\ge\delta^{(N)}>0$ and $\eta\in(0,1]$. Sample $E\sim\mathrm{Unif}(\mathrm{Gr}(\tilde d,d))$ and $E^{(\le N)}=\mathrm{NoiseAddition}(T(E),\delta^{(\le N)})$ as in Game 1. Then for $1\le i\le N$ the conditional law of $E^{(i)}$ given $E^{(\le i-1)}$ is dominated by
--   $$
--   e^{\,d\tilde d(\delta^{(i-1)}+\dots+\delta^{(N)})\kappa(T)}\cdot\mathrm{Unif}\big(B(E^{(i-1)},\delta^{(i-1)})\big),
--   $$
--   that is, for all measurable sets $A$ of subspaces and $B$ of histories,
--   $$
--   \Pr\big(E^{(i)}\in A,\ E^{(\le i-1)}\in B\big)\le\mathbb E\Big[e^{\,d\tilde d(\delta^{(i-1)}+\dots+\delta^{(N)})\kappa(T)}\,\mathrm{Unif}\big(B(E^{(i-1)},\delta^{(i-1)})\big)(A)\,\mathbf 1\{E^{(\le i-1)}\in B\}\Big].
--   $$
--
--   The posterior of the next version is thus essentially uniform on a Grassmannian ball around the previous one, which reduces the compression game to finding vectors nearly orthogonal to a uniform subspace in a ball (Lemma 14).
--
--   **Formalization Note** The parameter $\eta$ is kept as printed and does not enter the conclusion.
--
--   Differences from the source:
--   - encoding: density of E^(i) | E^(≤i−1) w.r.t. Haar ≤ e^{…} × density of Unif(B(E^(i−1), δ^(i−1))) → domination of the conditional law by e^{…} · Unif(B(E^(i−1), δ^(i−1))), in disintegration form; reason: a pointwise density bound w.r.t. the Haar measure is equivalent to this domination of measures
--   - encoding: a linear map T; accuracies δ^(≤N) → T invertible; 0 < δ^(N) ≤ … ≤ δ^(0); 1 ≤ i ≤ N; reason: T(E) must be d̃-dimensional and the balls nondegenerate for NoiseAddition to be defined; NoiseAddition takes nonnegative decreasing accuracies (p.7); E^(i−1) requires i ≥ 1
-- source:
--   Yu–Blanchard, Exponential memory/query-complexity tradeoffs in high-accuracy feasibility problems, preprint (Nov. 3, 2026), Lemma 13, p.25 (PDF p.26)

import Mathlib
import Definitions.Def_MemQueryFeas_IsGame1Nature
import Definitions.Def_MemQueryFeas_truncSeq
import Definitions.Def_MemQueryFeas_condNum

open MeasureTheory

namespace MemQueryFeas

/-- **Lemma 13 (posterior density bound).** Yu–Blanchard, *Exponential memory/query-complexity tradeoffs in high-accuracy feasibility problems*, preprint (Nov. 3, 2026), Lemma 13, p.25 (PDF p.26): "Fix a linear map `T`,
accuracies `δ^(≤N)`, and `η ∈ (0, 1]`. Sample `E ∼ Unif(Gr(d̃, d))` and `E^(≤N) := NoiseAddition(T(E),
δ^(≤N))` (as in Game 1). Then, `p_{E^(i)|E^(≤i−1)} ≤ e^{d d̃(δ^(i−1)+...+δ^(N))κ(T)} ·
p_{Unif(B(E^(i−1),δ^(i−1)))}`, where `p_A` denotes the density of the distribution of some random
variable `A` with respect to the Haar uniform measure."

For `1 ≤ i ≤ N`, the conditional law of `E^(i)` given `E^(≤i−1)` is dominated by
`e^{d d̃(δ^(i−1)+⋯+δ^(N))κ(T)}` times `Unif(B(E^(i−1), δ^(i−1)))`, in the disintegration form: for all
measurable `A` (subspaces) and `B` (histories),
`μ(E^(i) ∈ A, E^(≤i−1) ∈ B) ≤ ∫_{E^(≤i−1) ∈ B} e^{…} Unif(B(E^(i−1), δ^(i−1)))(A) dμ`.

**Formalization Note.** A density bound with respect to Haar measure is equivalent to this domination
of measures. `T` is invertible (otherwise `T(E)` is not `d̃`-dimensional and NoiseAddition is
undefined). The accuracies are positive and nonincreasing (the input of NoiseAddition, p.7). `η` is
kept as printed; it does not enter the conclusion. `E^(≤i−1)` is `truncSeq i`. -/
theorem lemma_13 {d dt N : ℕ} (T : Op d) (hT : IsUnit T) (δ : ℕ → ℝ)
    (hδpos : ∀ j ≤ N, 0 < δ j) (hδmono : ∀ j < N, δ (j + 1) ≤ δ j) (η : ℝ) (hη : 0 < η)
    (hη1 : η ≤ 1) {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ν : Measure (Op d)) (E : Ω → Op d) (ch : ℕ → Ω → Op d)
    (hnat : IsGame1Nature μ ν dt T δ N E ch) (i : ℕ) (hi1 : 1 ≤ i) (hiN : i ≤ N) :
    ∀ A : Set (Op d), MeasurableSet A → ∀ B : Set (ℕ → Op d), MeasurableSet B →
      μ (ch i ⁻¹' A ∩ (fun ω => truncSeq i (fun j => ch j ω)) ⁻¹' B) ≤
        ∫⁻ ω in (fun ω => truncSeq i (fun j => ch j ω)) ⁻¹' B,
          ENNReal.ofReal (Real.exp (d * dt * (∑ j ∈ Finset.Icc (i - 1) N, δ j) * condNum T)) *
            unifBall ν dt (ch (i - 1) ω) (δ (i - 1)) A ∂μ := by sorry

end MemQueryFeas
