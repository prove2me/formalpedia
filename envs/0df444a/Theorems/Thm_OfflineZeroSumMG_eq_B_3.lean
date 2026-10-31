-- Prove2me | Theorems.Thm_OfflineZeroSumMG_eq_B_3
-- name    : OfflineZeroSumMG.eq_B_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:28:46.284637+00:00
-- url     : https://prove2.me/theorems/423400e0-cb68-4b43-8bf4-e5faf094a5c5
-- title:
--   (B.3) — the matrix-game value map $Q\mapsto V$ is 1-Lipschitz in $\ell_\infty$
-- statement:
--   For a function $Q:\mathcal S\times\mathcal A\times\mathcal B\to\mathbb R$ let $V_Q(s)=\max_{\mu_s\in\Delta(\mathcal A)}\min_{\nu_s\in\Delta(\mathcal B)}\mathbb E_{a\sim\mu_s,b\sim\nu_s}[Q(s,a,b)]$ be the value function (3.3) associated with $Q$. For any $Q_1,Q_2:\mathcal S\times\mathcal A\times\mathcal B\to\mathbb R$,
--   $$\|V_{Q_1}-V_{Q_2}\|_\infty\le\|Q_1-Q_2\|_\infty.$$
--
--   This is what transfers contraction of the operators (3.4) from $Q$ to $V$, and it gives the first inequality of (B.7).
--
--   Differences from the source:
--   - encoding: $\mathcal S=\{1,\dots,S\}$, $\mathcal A=\{1,\dots,A\}$, $\mathcal B=\{1,\dots,B\}$ → `Fin S`, `Fin A`, `Fin B` (0-based) with $0<S$, $0<A$, $0<B$; reason: an index shift; same instances
--   - encoding: $\|\cdot\|_\infty$ → Mathlib's sup norm `‖·‖` on `Fin S → ℝ` and `Fin S → Fin A → Fin B → ℝ`; reason: on a finite product the sup norm is the $\ell_\infty$ norm
--   - encoding: $\max_{\mu_s\in\Delta(\mathcal A)}\min_{\nu_s\in\Delta(\mathcal B)}$ in (3.3) → real `⨆`/`⨅` over `stdSimplex` (`gval`, via the published `TheoryOfGames.Minimax.minK`); reason: the simplices are nonempty and compact and the payoff is continuous, so the sup and inf are the attained max and min
-- source:
--   Yan, Li, Chen & Fan, Model-Based Reinforcement Learning for Offline Zero-Sum Markov Games, arXiv:2206.04044v2 (https://arxiv.org/abs/2206.04044v2), §B.1 item 1, (B.3), p.14

import Mathlib
import Definitions.Def_OfflineZeroSumMG_VILCBGame

namespace OfflineZeroSumMG

/-- (B.3) (Yan, Li, Chen & Fan, arXiv:2206.04044v2, §B.1 item 1, p.14): for any
`Q₁, Q₂ : S × A × B → ℝ`, `‖V₁ − V₂‖_∞ ≤ ‖Q₁ − Q₂‖_∞`, where `V₁`, `V₂` are the value functions
(3.3) associated with `Q₁`, `Q₂`.

**Formalization Note.** `‖·‖` on `Fin S → ℝ` and on `Fin S → Fin A → Fin B → ℝ` is Mathlib's sup
norm of a finite product, i.e. `ℓ∞`. `Vof Q s = gval (Q s)` is the matrix-game value (3.3). -/
theorem eq_B_3 {S A B : ℕ} (hS : 0 < S) (hA : 0 < A) (hB : 0 < B)
    (Q₁ Q₂ : Fin S → Fin A → Fin B → ℝ) :
    ‖Vof Q₁ - Vof Q₂‖ ≤ ‖Q₁ - Q₂‖ := by sorry

end OfflineZeroSumMG
