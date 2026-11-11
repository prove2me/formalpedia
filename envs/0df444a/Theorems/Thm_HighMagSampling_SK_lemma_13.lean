-- Prove2me | Theorems.Thm_HighMagSampling_SK_lemma_13
-- name    : HighMagSampling.SK.lemma_13
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T18:29:20.603143+00:00
-- url     : https://prove2.me/theorems/ed480de1-c41c-4ecd-bdd9-2d5f75fe5016
-- title:
--   Lemma 13 — on the events of Lemma 12 and under (31): $\rho(4\beta J)\le C'\bar\beta^2\log(e\bar\beta)/d$ and $m(4\beta J)\le C'\bar\beta^2\Delta$
-- statement:
--   Let $C>0$ be the constant of Lemma 12. There is a universal constant $C'>0$ (depending only on $C$) with the following property. Let $d\ge1$, $\delta\in(0,\tfrac12)$, $\beta\ge0$, $\bar\beta=\max(\beta,1)$, and let $J$ be a symmetric $d\times d$ matrix with zero diagonal that satisfies Items 2, 3 and 4 of Lemma 12 with constant $C$. Put $K=4\beta J$ and $\Delta=\sqrt{\log(d/\delta)/d}+\log(d/\delta)/d$. If
--   $$\Delta\ \le\ \frac1{C'\bar\beta^2\log(e\bar\beta)}\qquad(31)$$
--   then
--   $$\rho(K)\le\frac{C'\bar\beta^2\log(e\bar\beta)}{d},\qquad m(K)\le C'\bar\beta^2\Delta .$$
--
--   Combined with Lemma 8 this gives the $\frac1{2k}$-Poincaré inequality for $k\lesssim d/(\bar\beta^2\log(e\bar\beta))$, the step that lets Theorem 4 hold at every temperature.
--
--   **Formalization Note.** The lemma is stated deterministically: the events are hypotheses on $J$, with an arbitrary constant $C>0$ quantified first. $\rho$, $m$, $\Delta$ and $\bar\beta$ are the mission's `rho`, `maxAbs`, `Delta`, `betaBar`.
--
--   Differences from the source:
--   - generalization: "assume the success of the events in Lemma 12" (for Lemma 12's constant $C$) → for every $C>0$ there is $C'$, for every $J$ satisfying Items 2–4 with constant $C$ (Item 1 is not assumed); reason: specializes to Lemma 12's $C$ and its event, on which Items 2–4 hold; the paper's proof uses only Items 2–4.
--   - reading: $J$ from Lemma 12 (Model 1, with a diagonal) under §4's standing assumption "$J$ has zero diagonal" → $J$ symmetric with $J_{ii}=0$; reason: §4 (p. 21) fixes the zero-diagonal convention for this section, and Lemma 7 requires $K_{ii}=0$.
--   - reading: $\beta\in\mathbb R_+$ → $\beta\ge0$; reason: the stronger reading of $\mathbb R_+$; $\beta=0$ gives $K=0$.
-- source:
--   Kumar, Sarkar, Tian, Zhu, High-Magnetization Sampling at Low Temperatures, arXiv:2609.08873v1, p. 26, Lemma 13, Eq. (31)

import Mathlib
import Definitions.Def_HighMagSampling_SK_Spectral
import Definitions.Def_HighMagSampling_SK_GOEEvents

namespace HighMagSampling.SK

/-- Lemma 13, p. 26: for every constant `C > 0` of Lemma 12 there is `C' > 0` such that for every
`d ≥ 1`, `δ ∈ (0, 1/2)`, `β ≥ 0` and symmetric zero-diagonal `J` on the events of Items 2–4 of
Lemma 12, condition (31) `Δ ≤ 1/(C' β̄² log(e β̄))` implies, with `K = 4βJ`,
`ρ(K) ≤ C' β̄² log(e β̄)/d` and `m(K) ≤ C' β̄² Δ`. -/
theorem lemma_13 :
    ∀ C : ℝ, 0 < C → ∃ C' : ℝ, 0 < C' ∧
      ∀ d : ℕ, 1 ≤ d → ∀ δ : ℝ, 0 < δ → δ < 1 / 2 → ∀ β : ℝ, 0 ≤ β →
        ∀ J : Matrix (Fin d) (Fin d) ℝ, J.IsSymm → (∀ i, J i i = 0) →
          event2 C d δ J → event3 C d δ J → event4 C d δ J →
          Delta d δ ≤ 1 / (C' * betaBar β ^ 2 * Real.log (Real.exp 1 * betaBar β)) →
            rho ((4 * β) • J) ≤ C' * betaBar β ^ 2 * Real.log (Real.exp 1 * betaBar β) / d ∧
              maxAbs ((4 * β) • J) ≤ C' * betaBar β ^ 2 * Delta d δ := by sorry

end HighMagSampling.SK
