-- Prove2me | Theorems.Thm_NoRegretLastIterate_lemma_3_7
-- name    : NoRegretLastIterate.lemma_3_7
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T13:33:45.112087+00:00
-- url     : https://prove2.me/theorems/6682ba39-39bd-4c33-a658-430945bbb2fa
-- title:
--   Lemma 3.7 — $\mathbb E|\overline Q_t-q^*|\le C/\sqrt t$ for two optimal no-regret players (corrected: in $L^1$, not pointwise)
-- statement:
--   Let $(G,H)$ be a competitive $2\times2$ game with Nash equilibrium $(p^*,q^*)$. Suppose player 1 uses a self-agnostic strategy $f$ with an optimal no-regret rate $(1/2,c)$ for $G$, player 2 a self-agnostic strategy $g$ with an optimal no-regret rate for $H$, and $(\Omega,\mu,I,J)$ carries their realization-based play. Then there is a constant $C>0$ such that for all $t\ge1$
--   $$
--   \mathbb E\,\big|\overline Q_t-q^*\big|\le\frac{C}{\sqrt t},\qquad \overline Q_t=\frac1t\sum_{s=1}^tQ_s .
--   $$
--
--   The time-average of the mixed strategies of two no-regret players approaches the set of coarse correlated equilibria (Roughgarden 2016), and in a competitive game that set is the single point $p^*\times q^*$. The rate $1/\sqrt t$ makes $\sqrt t(\overline Q_t-q^*)$ bounded in $L^1$, which is how the average enters the proof of Theorem 3.4.
--
--   **Formalization Note** $C$ depends on the game and the two strategies only: it is chosen before the probability space and works for every space carrying the play and every $t\ge1$. Player 2's regret is the row-player regret of $H^{\mathsf T}$.
--
--   Differences from the source:
--   - correction: |Q̄_t − q∗| ≤ C/√t pointwise, for all t ≥ 1 → E|Q̄_t − q∗| ≤ C/√t for all t ≥ 1; reason: false pointwise: in matching pennies with both players using Hedge with step 1/√t (mean-based, monotone, rate (1/2, c)), the event I₁ = … = I_t = 1 has positive probability and on it player 2 plays Q_s = 1/(1 + e^{2(s−1)/√s}) → 0, so |Q̄_t − q∗| → 1/2; App. B drops the martingale terms between realized and expected regret. The L¹ form is what the proof of (3.26) needs
--   - reading: "players 1 and 2 both use optimal no-regret strategies"; "a universal constant C > 0" → self-agnostic strategies with uniform no-regret rate (1/2, c) in the realization-based play; ∃ C > 0 independent of t and of the probability space carrying the play; reason: Definitions 2.1, 2.3 and the model of §2; "universal" is read as uniform in t (the constant depends on the game and the regret constants)
--   - encoding: uniform no-regret rate (r, c) for a finite c: lim sup_T max_J T^{−r} Reg_T(J) ≤ c → ∃ c, for all large T and all J, Reg_T(J) ≤ c·T^r; reason: equivalent, since the maximum over {0,1}^T is finite; avoids a real-valued limsup
--   - encoding: (p∗, q∗) a Nash equilibrium in mixed strategies; actions 0, 1 → published RankOneBimatrix.BinSearch.IsNE on the probability vectors (1 − p, p), (1 − q, q); actions Fin 2; reason: Lean convention and published vocabulary; same instances
--   - encoding: rounds t = 1, 2, …; f_t applied to (J)^{t−1} → Lean rounds n = t − 1 from 0; F n applied to the first n actions; reason: Lean convention; same instances
-- source:
--   Muthukumar, Phade, Sahai, On the Impossibility of Convergence of Mixed Strategies with Optimal No-Regret Learning, arXiv:2012.02125v3, Lemma 3.7, (3.25), p.19; proof App. B, pp.30–32

import Mathlib
import Definitions.Def_RankOneBimatrix_BinSearch_Game
import Definitions.Def_NoRegretLastIterate_Game
import Definitions.Def_NoRegretLastIterate_Strategy
import Definitions.Def_NoRegretLastIterate_Play

open MeasureTheory Matrix

universe u

namespace NoRegretLastIterate

/-- Muthukumar, Phade, Sahai, arXiv:2012.02125v3, Lemma 3.7, p.19, proof App. B pp.30–32
(corrected: in `L¹`, not pointwise). Suppose players 1 and 2 both use optimal no-regret
self-agnostic strategies `F₁`, `F₂` (rate `(1/2, c)`) in a competitive game `(G, H)` with Nash
equilibrium `(p∗, q∗)`, and `(Ω, μ, I, J)` carries their realization-based play. Then there is a
constant `C > 0`, the same for every probability space carrying the play, such that
`E|Q̄_t − q∗| ≤ C/√t` for all `t ≥ 1`, where `Q̄_t = (1/t) Σ_{s≤t} Q_s`.

**Formalization Note** The printed "|Q̄_t − q∗| ≤ C/√t pointwise" is false: in matching pennies
with both players using Hedge with step `1/√t`, the event `I_1 = … = I_t = 1` has positive
probability and on it `Q̄_t → 0`. Player 2's regret is the row-player regret of `Hᵀ`. -/
theorem lemma_3_7 {G H : Matrix (Fin 2) (Fin 2) ℝ} (hcomp : IsCompetitive G H) {p q : ℝ}
    (hNE : RankOneBimatrix.BinSearch.IsNE G H (mix p) (mix q))
    {F₁ F₂ : (n : ℕ) → (Fin n → Fin 2) → ℝ} (hF₁ : IsStrategy F₁) (hF₂ : IsStrategy F₂)
    (h₁ : HasRate G F₁ (1 / 2)) (h₂ : HasRate Hᵀ F₂ (1 / 2)) :
    ∃ C : ℝ, 0 < C ∧ ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
      (I J : ℕ → Ω → Fin 2), IsPlay μ F₁ F₂ I J → ∀ t : ℕ, 1 ≤ t →
        ∫ ω, |avgMixed F₂ I t ω - q| ∂μ ≤ C / Real.sqrt t := by sorry

end NoRegretLastIterate
