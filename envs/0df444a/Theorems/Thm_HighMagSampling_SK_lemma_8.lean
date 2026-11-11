-- Prove2me | Theorems.Thm_HighMagSampling_SK_lemma_8
-- name    : HighMagSampling.SK.lemma_8
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T18:28:28.848479+00:00
-- url     : https://prove2.me/theorems/f7a8464c-3b7f-4011-bdb1-55207d5a1ff2
-- title:
--   Lemma 8 — $\rho(4\beta J)e^{m(4\beta J)}\le 1/(2(k-1))$ gives a $1/(2k)$-Poincaré inequality for the fixed-magnetization Ising down-up walk
-- statement:
--   Let $d\ge1$, $k\in[d]$, $\beta>0$, $h\in\mathbb R^d$, and let $J\in\mathbb R^{d\times d}$ be symmetric with zero diagonal (the standing convention of §4). Let $\pi$ be the fixed-magnetization Ising measure $\pi(x)\propto\exp(\beta(\tfrac12x^\top Jx+h^\top x))$ on $\mathcal X^d_k$. With $m$ and $\rho$ as in Lemma 7, if
--   $$\rho(4\beta J)\,\exp\big(m(4\beta J)\big)\ \le\ \frac1{2(k-1)},$$
--   then the down-up walk $\mathcal T^{\mathrm{DU},\pi}$ satisfies a $\frac1{2k}$-Poincaré inequality.
--
--   This is the bridge from the interaction matrix to the mixing of the down-up walk: Lemma 13 verifies the hypothesis for the SK model, and Lemma 1 turns the conclusion into a mixing bound.
--
--   **Formalization Note.** $4\beta J$ is the scalar multiple `(4 * β) • J`. The hypothesis is cleared of its denominator.
--
--   Differences from the source:
--   - encoding: $\rho(4\beta J)\exp(m(4\beta J))\le\frac1{2(k-1)}$ → $2(k-1)\,\rho(4\beta J)\exp(m(4\beta J))\le1$; reason: the same condition for $k\ge2$; no division by $0$.
--   - generalization: $k\ge2$ implicit in $\frac1{2(k-1)}$ → every $k\in[d]$, the hypothesis being vacuous at $k=1$; reason: at $k=1$ the down-up walk samples $\pi$ exactly, so the $\tfrac12$-Poincaré inequality holds; for $k\ge2$ it is the source's statement.
--   - encoding: $\mathcal X^d_k$ as $\pm1$ vectors → `Slice d k`; reason: the paper's bijection $x\mapsto\mathrm{set}(x)$.
-- source:
--   Kumar, Sarkar, Tian, Zhu, High-Magnetization Sampling at Low Temperatures, arXiv:2609.08873v1, p. 21, Lemma 8 (with the §4 zero-diagonal convention, p. 21)

import Mathlib
import Definitions.Def_HighMagSampling_SK_MarkovChain
import Definitions.Def_HighMagSampling_SK_DownUp
import Definitions.Def_HighMagSampling_SK_Spectral

namespace HighMagSampling.SK

/-- Lemma 8, p. 21: for the fixed-magnetization Ising measure `π` on `X^d_k` with symmetric,
zero-diagonal `J`, if `ρ(4βJ) exp(m(4βJ)) ≤ 1/(2(k − 1))` then `T^{DU,π}` satisfies a
`1/(2k)`-Poincaré inequality. The hypothesis is written `2(k − 1) ρ(4βJ) exp(m(4βJ)) ≤ 1`. -/
theorem lemma_8 (d k : ℕ) (hk : 1 ≤ k) (hkd : k ≤ d) (β : ℝ) (hβ : 0 < β)
    (J : Matrix (Fin d) (Fin d) ℝ) (hJ : J.IsSymm) (hdiag : ∀ i, J i i = 0) (h : Fin d → ℝ)
    (hcond : 2 * ((k : ℝ) - 1) * (rho ((4 * β) • J) * Real.exp (maxAbs ((4 * β) • J))) ≤ 1) :
    SatisfiesPoincare (downUp (isingMeasure k β J h)) (isingMeasure k β J h) (1 / (2 * k)) := by sorry

end HighMagSampling.SK
