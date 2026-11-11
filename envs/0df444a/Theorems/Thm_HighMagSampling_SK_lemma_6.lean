-- Prove2me | Theorems.Thm_HighMagSampling_SK_lemma_6
-- name    : HighMagSampling.SK.lemma_6
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T18:29:12.548574+00:00
-- url     : https://prove2.me/theorems/6f77ace6-aa6e-4d08-bccb-8ea0f1adc8b6
-- title:
--   Lemma 6 (trickle down) — $\lambda_2(P_R)\le\alpha/(k-1)$ for all links gives a $(1-\alpha)/k$-Poincaré inequality for the down-up walk
-- statement:
--   Let $d\ge1$, $k\in[d]$, and let $\pi$ be a probability measure on $\mathcal X^d_k$ with full support. For $R\subseteq[d]$ with $|R|=k-2$ let $P_R$ be the random walk matrix of the link graph of $R$ (vertices $[d]\setminus R$, weights $\pi(R\cup\{i,j\})$). If for some $\alpha<1$
--   $$\lambda_2(P_R)\ \le\ \frac{\alpha}{k-1}\qquad\text{for all }R\in\binom{[d]}{k-2},$$
--   then the down-up walk $\mathcal T^{\mathrm{DU},\pi}$ satisfies a $\lambda$-Poincaré inequality with
--   $$\lambda=\frac{1-\alpha}{k}.$$
--
--   This is the trickle-down theorem of Oppenheim and Alev–Lau in the form the paper uses; with Lemma 7 it reduces the Poincaré constant of the down-up walk to spectral bounds on small link graphs. As printed it is false at $k=1$ for $\alpha<0$ (the family of links is empty there); this is recorded as a finding and the statement is posed as printed.
--
--   **Formalization Note.** The family $\binom{[d]}{k-2}$ is written as the sets $R$ with $|R|+2=k$, so it is empty at $k=1$ as on the page (no natural-number subtraction), and the bound $\lambda_2(P_R)\le\alpha/(k-1)$ is written $(k-1)\lambda_2(P_R)\le\alpha$, so no division by $0$ occurs. $\lambda_2(P_R)$ is `lambdaTwoRW` of the link weights.
--
--   Differences from the source:
--   - encoding: $R\in\binom{[d]}{k-2}$ → `R.card + 2 = k`; reason: the same family for $k\ge2$ and empty at $k=1$, avoiding truncated subtraction.
--   - encoding: $\lambda_2(P_R)\le\alpha/(k-1)$ → $(k-1)\,\lambda_2(P_R)\le\alpha$; reason: equivalent for $k\ge2$; at $k=1$ there is no $R$, so the bound is never evaluated.
--   - encoding: $\lambda_2(P_R)$ → $\lambda_2$ with multiplicity of $D^{-1/2}WD^{-1/2}$; reason: similar to $P_R$ (degrees are positive under full support and $|[d]\setminus R|\ge2$), as in the paper's proof of Lemma 7.
--   - encoding: $\mathcal X^d_k$ as $\pm1$ vectors → `Slice d k`; reason: the paper's bijection $x\mapsto\mathrm{set}(x)$.
-- source:
--   Kumar, Sarkar, Tian, Zhu, High-Magnetization Sampling at Low Temperatures, arXiv:2609.08873v1, p. 19, Lemma 6

import Mathlib
import Definitions.Def_HighMagSampling_SK_MarkovChain
import Definitions.Def_HighMagSampling_SK_DownUp
import Definitions.Def_HighMagSampling_SK_Spectral

open MeasureTheory ProbabilityTheory

namespace HighMagSampling.SK

/-- Lemma 6, p. 19 (trickle down): for `π ∈ P(X^d_k)` with full support, if
`λ₂(P_R) ≤ α/(k − 1)` for every `R ⊆ [d]` with `|R| = k − 2`, for some `α < 1`, then `T^{DU,π}`
satisfies a `(1 − α)/k`-Poincaré inequality. The hypothesis is written `(k − 1) λ₂(P_R) ≤ α`
over the `R` with `|R| + 2 = k`. -/
theorem lemma_6 (d k : ℕ) (hk : 1 ≤ k) (hkd : k ≤ d) (π : Measure (Slice d k))
    [IsProbabilityMeasure π] (hfull : ∀ S : Slice d k, π {S} ≠ 0) (α : ℝ) (hα : α < 1)
    (hlink : ∀ R : Finset (Fin d), R.card + 2 = k →
      ((k : ℝ) - 1) * lambdaTwoRW (linkWeight π R) ≤ α) :
    SatisfiesPoincare (downUp π) π ((1 - α) / k) := by sorry

end HighMagSampling.SK
