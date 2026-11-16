-- Prove2me | Theorems.Thm_OptHedgeGames_Supplement_theorem_3_6
-- name    : OptHedgeGames.Supplement.theorem_3_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T04:22:10.240162+00:00
-- url     : https://prove2.me/theorems/cbd13ff6-4b3f-4f72-b0a4-deb7c06f8d61
-- title:
--   Theorem 3.6 — an exponential barrier for three players, $\sup_T\mathrm{Reg}_3(T)\ge2^{n/8}\log n/(C_0n)-1$, and linear regret for $\eta\ge C_0n2^{-n/8}$
-- statement:
--   There are absolute constants $C_0>0$ and $\eta_0>0$ with the following three properties, where
--   $$
--   B(n)=\frac{2^{n/8}\log n}{C_0\,n}-1 .
--   $$
--   1. For every $n\ge C_0$ and every $\eta\in(0,\eta_0]$ there is a three-player game $G\in\mathcal G(3,n)$ in which, when all players run Optimistic Hedge with learning rate $\eta$ from the uniform distribution,
--   $$
--   \sup_{T\ge1}\mathrm{Reg}_3(T)\ge B(n).
--   $$
--   2. In particular, for every $n\ge C_0$,
--   $$
--   \inf_{0<\eta\le\eta_0}\ \sup_{T\ge1}\ \sup_{G\in\mathcal G(3,n)}\ \max_i\mathrm{Reg}_i(T)\ge B(n).
--   $$
--   3. If moreover $\eta\ge C_0\,n\,2^{-n/8}$, then $G$ can be chosen so that player 3's regret grows linearly: there are $c=c(G,\eta)>0$ and $C=C(G,\eta)$ with $\mathrm{Reg}_3(T)\ge cT-C$ for all $T\ge1$.
--
--   Since $B(n)=2^{\Omega(n)}$, no bound polynomial in $n$, uniform in the horizon, holds for three players, in contrast with the two-player bound of the mission's goal.
--
--   **Formalization Note** Player 3 is `2 : Fin 3`; $2^{n/8}$ is a real power and $\log$ the natural logarithm. A supremum bound $\sup\ge B$, where the supremum may be $+\infty$, is stated as: for every $\varepsilon>0$ some term is at least $B-\varepsilon$.
--
--   Differences from the source:
--   - reading: $\sup_T\mathrm{Reg}_3(T)\ge B$ and the inf–sup–sup–max bound → for every $\varepsilon>0$ some horizon (and game and player) has regret $\ge B-\varepsilon$, for every $\eta\in(0,\eta_0]$; reason: the suprema may be $+\infty$, and this is exactly "$\sup\ge B$" without a real-valued supremum.
--   - encoding: absolute constants $C_0$ and $\eta_0>0$ → $C_0>0$ explicit; reason: the paper divides by $C_0n$ and requires $n\ge C_0$ with $n$ a number of actions; a nonpositive $C_0$ makes the bound undefined.
--   - encoding: player 3, horizons $T$ → `2 : Fin 3`, $T\ge1$; reason: 0-based players; the paper's horizons are $T\ge1$.
-- source:
--   Dagan, Eisen, Erez & Koren, Optimistic Hedge in General-Sum Games, STOC 2027 submission manuscript (sha256 383e3793…), Theorem 3.6, p.10

import Mathlib
import Definitions.Def_OptHedgeGames_Supplement_MultiRun

namespace OptHedgeGames

namespace Supplement

/-- **Theorem 3.6 (An exponential barrier for three players).** There are absolute constants `C₀`
and `η₀ > 0` such that for every `n ≥ C₀` and every learning rate `η ∈ (0, η₀]` there is a
three-player game `G ∈ G(3, n)` in which, when all players run Optimistic Hedge with learning rate
`η` from the uniform distribution, `sup_T Reg₃(T) ≥ 2^{n/8} log n/(C₀ n) − 1`. In particular
`inf_{0<η≤η₀} sup_{T≥1} sup_{G∈G(3,n)} maxᵢ Regᵢ(T) ≥ 2^{n/8} log n/(C₀n) − 1`. Moreover, if
`η ≥ C₀ n 2^{−n/8}`, then `G` can be chosen so that `Reg₃(T) ≥ cT − C` for all `T`, for some
`c = c(G, η) > 0` and `C = C(G, η)`
(Dagan, Eisen, Erez & Koren, *Optimistic Hedge in General-Sum Games*, STOC 2027 submission
manuscript (sha256 383e3793…), Theorem 3.6, p.10).

**Formalization Note** Players are `Fin 3`; player 3 is `2 : Fin 3`. `log` is `Real.log`, `2^{n/8}`
is the real power `(2 : ℝ) ^ ((n : ℝ) / 8)`. A supremum `sup_T Reg(T) ≥ B` (which may be `+∞`) is
stated as `∀ ε > 0, ∃ T ≥ 1, Reg(T) ≥ B − ε`, and the infimum over `η` as `∀ η`. The same `C₀ > 0`
appears in the threshold `n ≥ C₀`, in the bound, and in the threshold `η ≥ C₀ n 2^{−n/8}`;
`c, C` are chosen after `G` and `η`. Horizons are `T ≥ 1`. -/
theorem theorem_3_6 :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∃ η₀ : ℝ, 0 < η₀ ∧
      (∀ n : ℕ, C₀ ≤ (n : ℝ) → ∀ η : ℝ, 0 < η → η ≤ η₀ →
        ∃ G : MGame 3 n, ∀ ε : ℝ, 0 < ε → ∃ T : ℕ, 1 ≤ T ∧
          (2 : ℝ) ^ ((n : ℝ) / 8) * Real.log (n : ℝ) / (C₀ * (n : ℝ)) - 1 - ε ≤ G.Reg η 2 T) ∧
      (∀ n : ℕ, C₀ ≤ (n : ℝ) → ∀ η : ℝ, 0 < η → η ≤ η₀ → ∀ ε : ℝ, 0 < ε →
        ∃ G : MGame 3 n, ∃ T : ℕ, 1 ≤ T ∧ ∃ i : Fin 3,
          (2 : ℝ) ^ ((n : ℝ) / 8) * Real.log (n : ℝ) / (C₀ * (n : ℝ)) - 1 - ε ≤ G.Reg η i T) ∧
      (∀ n : ℕ, C₀ ≤ (n : ℝ) → ∀ η : ℝ, 0 < η → η ≤ η₀ →
        C₀ * (n : ℝ) * (2 : ℝ) ^ (-(n : ℝ) / 8) ≤ η →
        ∃ G : MGame 3 n, ∃ c : ℝ, 0 < c ∧ ∃ C : ℝ, ∀ T : ℕ, 1 ≤ T →
          c * (T : ℝ) - C ≤ G.Reg η 2 T) := by sorry

end Supplement

end OptHedgeGames
