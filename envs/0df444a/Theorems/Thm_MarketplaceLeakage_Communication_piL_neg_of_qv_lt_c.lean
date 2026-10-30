-- Prove2me | Theorems.Thm_MarketplaceLeakage_Communication_piL_neg_of_qv_lt_c
-- name    : MarketplaceLeakage.Communication.piL_neg_of_qv_lt_c
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T01:04:10.105253+00:00
-- url     : https://prove2.me/theorems/be15818e-2abb-4c26-9247-24f03c4a8b51
-- title:
--   If $qv<c$ then $\Pi_L(\eta)<0$, so M chooses option 1
-- statement:
--   A marketplace $M$ intermediates the sales of a seller $S$ whose product buyers value at $v$; $S$ has marginal cost $c$ with $0<c<v$ and pays $M$ a per-transaction fee $f$. A priori a buyer values the product at $v$ with probability $q\in(0,1)$ and at zero otherwise. If $M$ bans buyer–seller communication, buyers can no longer buy directly from $S$ (no leakage), but each buyer learns their true valuation only with probability $\eta\in[0,1]$.
--
--   Let $0<c<v$ and $0<q<1$, and suppose $qv<c$. Then
--
--   $$
--   \Pi_L(\eta)<0\quad\text{for every }\eta\in[0,1),
--   $$
--
--   and the marketplace's ban profit is that of option 1: $\max\{\Pi_H(\eta),\Pi_L(\eta)\}=\Pi_H(\eta)$ for every $\eta\in[0,1]$.
--
--   This is the first case of the proof of Proposition 3: when the expected value $qv$ is below cost, the low-price option is never profitable.
--
--   Differences from the source:
--
--   - encoding: Π_L(η) < 0 for all η ∈ [0, 1] → Π_L(η) < 0 for η ∈ [0, 1); the option-1 claim on all of [0, 1]; reason: Π_L is undefined at η = 1; there Lean's x/0 = 0 gives Π_L(1) = −qc < 0 and the ban profit is Π_H(1), as in the paper
--   - reading: "M chooses option 1" → max{Π_H(η), Π_L(η)} = Π_H(η); reason: option 1 earns Π_H and M's ban profit is the maximum of the two options (p. 15)
-- source:
--   Hagiu, Wright, Marketplace Leakage, authors' manuscript (March 2023), doi:10.1287/mnsc.2023.4757, §8.4 (proof of Proposition 3), unnumbered, p. 38

import Mathlib
import Definitions.Def_MarketplaceLeakage_Communication_banProfit

namespace MarketplaceLeakage.Communication

/-- **If `qv < c` then `Π_L(η) < 0`, so M chooses option 1.**
Hagiu, Wright, *Marketplace Leakage*, authors' manuscript (March 2023), §8.4 (proof of Proposition 3), unnumbered, p. 38: "If qv < c, then ΠL (η) < 0 for all
η ∈ [0, 1], so M chooses option 1 for all η ∈ [0, 1]."

Standing assumptions `0 < c < v` (pp. 5–6), `0 < q < 1` (p. 14). If `qv < c` then
`Π_L(η) < 0` for every `η ∈ [0, 1)`, and the ban profit equals `Π_H(η)` (option 1) for every
`η ∈ [0, 1]`.

**Formalization Note.** The paper's `Π_L` is undefined at `η = 1` (division by `1 − η`), so
the sign claim is stated on `[0, 1)`. The "option 1" claim is stated on `[0, 1]`: at `η = 1`
Lean's `x / 0 = 0` gives `piL = −qc < 0`, and the ban profit is `Π_H(1)`, as in the paper. -/
theorem piL_neg_of_qv_lt_c {q v c : ℝ} (hc : 0 < c) (hcv : c < v) (hq0 : 0 < q) (hq1 : q < 1)
    (hqv : q * v < c) :
    (∀ η : ℝ, 0 ≤ η → η < 1 → piL q v c η < 0) ∧
      (∀ η : ℝ, 0 ≤ η → η ≤ 1 → banProfit q v c η = piH q v c η) := by sorry

end MarketplaceLeakage.Communication
