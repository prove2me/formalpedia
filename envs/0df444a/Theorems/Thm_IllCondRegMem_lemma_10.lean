-- Prove2me | Theorems.Thm_IllCondRegMem_lemma_10
-- name    : IllCondRegMem.lemma_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T09:57:46.459838+00:00
-- url     : https://prove2.me/theorems/b38e28e1-fa9f-4bdb-bb64-5d775de9a108
-- title:
--   Lemma 10 — hardness of the orthogonal vector game: $\mathbb E[\sigma_k^p]\le2^{M+kd}\delta_{\max}^{k(d_E-m-k+1-p)}$
-- statement:
--   Consider Game 1 with dimensions $d\ge d_E$, message size $M$, query size $m$, accuracy $\delta_{\max}\in(0,1]$ and target $k$. For any possibly randomized strategy and any $p$ with $0<p\le d_E-m-k+1$, the final score $\sigma_k$ satisfies
--   $$
--   \mathbb E[\sigma_k^p]\le 2^{M+kd}\,\delta_{\max}^{\,k(d_E-m-k+1-p)} .
--   $$
--   A player can score highly only by storing about $kd_E$ bits about $E$ or by seeing about $d_E$ vectors of $E$; this forces every phase of the masked adversary to last $\Omega(d)$ rounds.
--
--   **Formalization Note** Strategies and $\mathbb E[\sigma_k^p]$ are as in the definition of Game 1 (Gaussian column span for the uniform subspace, one private seed, invalid queries lose). The final score is assumed to be a measurable function of the randomness, so that its moment is an expectation.
--
--   Differences from the source:
--   - reading: "Algorithm 1" → Game 1; reason: the paper's label for the orthogonal vector game (p.10)
--   - generalization: the player uses "all stage 2 history" → the player sees the earlier responses P_{E⊥}w_j as vectors; reason: the proof (p.32) conditions on these vectors; more information enlarges the strategy class and specializes to the paper's
--   - encoding: E ∼ Unif(Gr(d_E, d)), v_i ∼ N(0, P_E), randomized strategy, E[σ_k^p] → Gaussian column span, v_i = P_E g_i, one uniform private seed, lower integral of σ_k^p in [0, ∞]; reason: the Gaussian column span is rotation invariant of dimension d_E a.s.; same law
--   - encoding: submissions must lie in S^{d−1} ∩ G⊥ × (0, δ_max] → an invalid submission loses (σ = 0); reason: such strategies are pointwise dominated by valid ones, so the bound is unchanged
--   - encoding: a (measurable) randomized strategy, for which E[σ_k^p] is an expectation → the final score is a measurable function of (Gaussian columns, v-Gaussians, seed); reason: excludes only strategies whose moment is undefined (without it the lower integral would quantify over non-measurable players the source does not consider)
-- source:
--   M. Blanchard, D. Hansen, A. Jayant, V. Sharan, Polynomial Memory-Sample Separations in Non-i.i.d. Ill-Conditioned Regression, STOC 2027 submission (held version, sha256 6369d09f…), Lemma 10, p.11 (PDF p.12); Game 1, p.10 (PDF p.11); restated p.32 (PDF p.33)

import Mathlib
import Definitions.Def_IllCondRegMem_ovgMoment

open MeasureTheory ProbabilityTheory

namespace IllCondRegMem

/-- **Lemma 10 (Orthogonal vector game hardness).**
Blanchard, Hansen, Jayant, Sharan, *Polynomial Memory-Sample Separations in Non-i.i.d.
Ill-Conditioned Regression*, STOC 2027 submission (held version, sha256 6369d09f…), Lemma 10,
p.11 (restated p.32): "For any possibly randomized strategy for Algorithm 1 has the pth moment
(0 < p ≤ d_E − m − k + 1) of its final score σ_k, at most E[σ_k^p] ≤ 2^{M+kd} δ_max^{k(d_E−m−k+1−p)}."

**Formalization Note.** "Algorithm 1" is Game 1 (p.10), with its inputs `d ≥ d_E`,
`δ_max ∈ (0, 1]`, message size `M`, query size `m` and target `k`. A strategy is an
`OVGStrategy` (randomized through one private uniform seed); `E[σ_k^p]` is `ovgMoment`
(uniform subspace as a Gaussian column span, invalid queries lose). The final score is required
to be a measurable function of the oracle's and the player's randomness (`hmeas`), so that
`E[σ_k^p]` is an expectation; this excludes only strategies for which the moment is undefined. -/
theorem lemma_10 (d dE M m k : ℕ) (δmax p : ℝ) (S : OVGStrategy d M m k) (hdE : dE ≤ d)
    (hδ0 : 0 < δmax) (hδ1 : δmax ≤ 1) (hp0 : 0 < p) (hp : p ≤ (dE : ℝ) - m - k + 1)
    (hmeas : Measurable fun ζ : (Fin dE → Vec d) × (Fin m → Vec d) × unitInterval =>
      (ovgRun S δmax (Submodule.span ℝ (Set.range ζ.1))
        (fun i => (Submodule.span ℝ (Set.range ζ.1)).starProjection (ζ.2.1 i)) ζ.2.2 k).1) :
    ovgMoment dE S δmax p ≤
      ENNReal.ofReal ((2 : ℝ) ^ (M + k * d) * δmax ^ ((k : ℝ) * ((dE : ℝ) - m - k + 1 - p))) := by sorry

end IllCondRegMem
