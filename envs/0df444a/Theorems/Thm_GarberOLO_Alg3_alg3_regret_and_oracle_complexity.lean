-- Prove2me | Theorems.Thm_GarberOLO_Alg3_alg3_regret_and_oracle_complexity
-- name    : GarberOLO.Alg3.alg3_regret_and_oracle_complexity
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T00:06:02.772287+00:00
-- url     : https://prove2.me/theorems/598ef66d-48d6-42ae-bc51-cbf4c641aa91
-- title:
--   Theorem 1 [Main Theorem] (corrected: floors $\max\{1,d\}^2$, $\max\{1,\ln\}$ in the oracle bound)
-- statement:
--   Throughout, $K, \mathcal F \subset \mathbb R^d_+$ are compact, $\|x\| \le R$ on $K$, $\|f\| \le F$ on $\mathcal F$, $0 \le x\cdot f \le C$ on $K \times \mathcal F$ ($R, F, C > 0$), and $\mathcal O_K$ is an $\alpha$-approximate linear optimization oracle for $K$ ($\alpha > 0$; §2.1).
--
--   There is $c_0 > 0$ such that for every procedure constant $c \ge c_0$ there is $C > 0$ with the following property. Let $s_1 \in K$, $\eta > 0$, $\varepsilon \in (0, (\alpha+2)R]$, $T \ge 1$ and let $f_1, \dots, f_T \in \mathcal F$ be fixed in advance. Run Algorithm 3 for $T$ rounds (Algorithm 2 with $N$ prescribed as in Lemma 5 and an optimal solution of Problem (5)), and let $s_1, \dots, s_T$ be the played points. Then:
--
--   1. every call of Algorithm 2 in rounds $1, \dots, T$ terminates;
--   2. the expected α-regret satisfies
--   $$\mathbb E\big[\alpha\text{-regret}(\{(s_t, f_t)\}_{t\in[T]})\big] \le \frac{\alpha^2R^2}{T\eta} + \frac{\eta F^2}{2} + 3F\varepsilon;$$
--   3. the average number of oracle calls per round satisfies
--   $$K(\eta, \varepsilon) := \frac1T\sum_{t=1}^{T-1}\mathrm{calls}_t \le C\Big(1 + \frac{\eta\alpha RF + \eta^2F^2}{\varepsilon^2}\Big)\max\{1,d\}^2 \max\Big\{1, \ln\frac{(\alpha+1)R}{\varepsilon}\Big\};$$
--   4. if $\eta = \alpha R T^{-2/3}/F$ and $\varepsilon = \alpha R T^{-1/3}$, then $\mathbb E[\alpha\text{-regret}] \le \tfrac92\,\alpha RF\,T^{-1/3}$ and $K \le C\max\{1,d\}^2 \ln\big(\tfrac{\alpha+1}{\alpha}T\big)$;
--   5. if $\eta = \alpha R T^{-1/2}/F$ and $\varepsilon = \alpha R T^{-1/2}$, then $\mathbb E[\alpha\text{-regret}] \le \tfrac92\,\alpha RF\,T^{-1/2}$ and $K \le C\sqrt T\max\{1,d\}^2 \ln\big(\tfrac{\alpha+1}{\alpha}T\big)$.
--
--   The constants $c_0$ and $C$ depend on nothing (respectively, only on $c$). Online linear optimization with only an $\alpha$-approximation oracle thus achieves expected α-regret $O(T^{-1/3})$ with $O(d^2\log T)$ oracle calls per round on average, or $O(T^{-1/2})$ with $O(\sqrt T d^2 \log T)$.
--
--   Differences from the source:
--   - correction: K(η, ε) = O((1 + (ηαRF + η²F²)/ε²) d² ln((α+1)R/ε)); special cases K = O(d² ln((α+1)T/α)) and O(√T d² ln((α+1)T/α)) → C (1 + (ηαRF + η²F²)/ε²) max{1,d}² max{1, ln((α+1)R/ε)}; C max{1,d}² ln((α+1)T/α) and C √T max{1,d}² ln((α+1)T/α); reason: the printed bound is false: d = 1, K = 𝓕 = {1}, R = F = C = α = 1, O_K ≡ 1, η = 1, ε = 2 = (α+1)R ≤ (α+2)R, T = 2 satisfy every assumption; round 1 makes one oracle call, so the average is 1/2, while the printed bound is C·(3/2)·ln 1 = 0; for d = 0 the factor d² is 0 in all three bounds while T = 2 forces an average ≥ 1/2; the floors change nothing for d ≥ 1 and ε ≤ (α+1)R/e (paper.md Correction 1)
--   - generalization: c a (fixed) positive universal constant for which Lemma 5 holds → ∃ c₀ > 0, ∀ c ≥ c₀, ∃ C > 0 (C depends only on c); reason: every c ≥ c₀ satisfies Lemma 5's requirement, so the statement specializes to the paper's c (paper.md Reading 2)
--   - generalization: "Suppose Algorithm 3 is applied for T rounds" (termination presupposed) → clause 1: every Algorithm 2 call of rounds 1, …, T terminates; reason: the conclusion states what the paper presupposes (it follows from Lemma 7), so no unproved assumption sits in the definitions (paper.md item 9)
--   - generalization: E[α − regret] = O(αRF T^{−1/3}) and O(αRF T^{−1/2}) in the special cases → ≤ (9/2) αRF T^{−1/3} and ≤ (9/2) αRF T^{−1/2}; reason: explicit constants are stronger than O(·); they follow from the main bound (paper.md item 10)
--   - encoding: O(·) and "c is a positive universal constant" → ∃ c₀ > 0, ∀ c ≥ c₀, ∃ C > 0 quantified before d and every datum of the instance; reason: C may depend only on the universal constant c, which is the meaning of O(·) here
--   - reading: "the average number of calls to the approximation oracle of K per iteration" → avgCalls = (1/T) Σ_{t=1}^{T−1} calls_t, calls_t the O_K calls of round t's Algorithm 2 call; reason: the proof (p. 15) sums over t = 1, …, T−1 and divides by T; the round-T call only produces s_{T+1}, which is never played (paper.md Reading 3)
--   - encoding: E[α − regret] over the sampling of line 9 (oblivious adversary) → expectedRegret: the finite sum over sample paths σ of (∏_t a^{(t)}_{σ_t}) · α-regret(s₁, s^{(1)}_{σ₁}, …); reason: the law of (s₁, …, s_T) is the product of the per-round finite distributions; this is its expectation written out (paper.md Reading 4)
--   - reading: "the Ellipsoid method" (Lemma 5, p. 9), not specified further → the central-cut Ellipsoid method from E₀ = B(0,1) (ellipsoidCut, sdState), with bisection for d = 1 and no change on a zero cut vector; reason: E₀ = B(0,1) is the ball of Problem (4)'s constraint, which the proof on p. 11 needs (B(h/2, r) ⊂ B(0,1)); the standard update divides by d² − 1 = 0 when d = 1; a zero cut arises only when v = x, and then p = x (paper.md Reading 1)
--   - reading: N "as prescribed in Lemma 5" (Algorithm 2, line 8), any positive integer N ≥ c d² ln(((α+1)R + ‖x‖)/ε) → N = Nprescribed S c ε ỹ = max{1, ⌈c d² ln(((α+1)R + ‖ỹ‖)/ε)⌉}, recomputed at the current ỹ of each loop pass; reason: with N unbounded the oracle-call count is unbounded, so the least admissible N is the only reading under which the call bounds can hold (paper.md Reading 2)
--   - reading: "an optimal solution" of Problem (5), "some point" s₁ ∈ K, and the oracle O_K → arbitrary: every selector sel with IsOptimalSelector sel, every s₁ ∈ K, every OK with IsApproxOracle S OK; reason: the paper leaves these choices free and claims the result for every choice (paper.md Reading 5)
--   - encoding: "T rounds" (and division by T) → 1 ≤ T; reason: T rounds with a division by T presuppose T ≥ 1 (paper.md item 11)
-- source:
--   Garber, Efficient Online Linear Optimization with Approximation Algorithms, arXiv:1709.03093v1, Theorem 1 [Main Theorem], p. 14 (proof pp. 14–15)

import Mathlib
import Definitions.Def_GarberOLO_Alg3_Setting
import Definitions.Def_GarberOLO_Alg3_IsApproxOracle
import Definitions.Def_GarberOLO_Alg3_IsOptimalSelector
import Definitions.Def_GarberOLO_Alg3_alg2Terminates
import Definitions.Def_GarberOLO_Alg3_alg3Input
import Definitions.Def_GarberOLO_Alg3_expectedRegret
import Definitions.Def_GarberOLO_Alg3_avgCalls

namespace GarberOLO.Alg3

/-- **Theorem 1 [Main Theorem] (corrected: floors max{1,d}² and max{1, ln((α+1)R/ε)} in the
oracle bound).**
Garber, *Efficient Online Linear Optimization with Approximation Algorithms*, arXiv:1709.03093v1, Theorem 1, p. 14: "Fix η > 0, ε ∈ (0, (α + 2)R]. Suppose Algorithm 3 is applied for T rounds
and let {f_t}_{t=1}^T ⊆ 𝓕 be the sequence of observed loss/payoff vectors, and let {s_t}_{t=1}^T be
the sequence of points played by the algorithm. Then it holds that
E[α − regret({(s_t, f_t)}_{t∈[T]})] ≤ α²R²/(Tη) + ηF²/2 + 3Fε, and the average number of calls to
the approximation oracle of K per iteration is upper bounded by
K(η, ε) := O((1 + (ηαRF + η²F²)/ε²) d² ln((α + 1)R/ε)). In particular, setting
η = αRT^{−2/3}/F, ε = αRT^{−1/3} gives E[α − regret] = O(αRF T^{−1/3}), K = O(d² ln((α+1)T/α)).
Alternatively, setting η = αRT^{−1/2}/F, ε = αRT^{−1/2} gives E[α − regret] = O(αRF T^{−1/2}),
K = O(√T d² ln((α+1)T/α))."

There is `c₀ > 0` such that for every procedure constant `c ≥ c₀` there is `C > 0` such that,
for every dimension `d`, every instance `S` of the §2.1 setting, every oracle `OK` with the §2.1
guarantee, every optimal selector `sel` for Problem (5), every `s₁ ∈ K`, `η > 0`,
`ε ∈ (0, (α+2)R]`, `T ≥ 1` and `f₁, …, f_T ∈ 𝓕`, Algorithm 3 satisfies:
1. every Algorithm 2 call of rounds 1, …, T terminates;
2. `E[α-regret] ≤ α²R²/(Tη) + ηF²/2 + 3Fε`;
3. `(1/T) Σ_{t=1}^{T−1} calls_t ≤ C (1 + (ηαRF + η²F²)/ε²) max{1,d}² max{1, ln((α+1)R/ε)}`;
4. if `η = αRT^{−2/3}/F` and `ε = αRT^{−1/3}`: `E[α-regret] ≤ (9/2) αRF T^{−1/3}` and
   `(1/T) Σ calls_t ≤ C max{1,d}² ln((α+1)T/α)`;
5. if `η = αRT^{−1/2}/F` and `ε = αRT^{−1/2}`: `E[α-regret] ≤ (9/2) αRF T^{−1/2}` and
   `(1/T) Σ calls_t ≤ C √T max{1,d}² ln((α+1)T/α)`.

**Formalization Note.** `C` is chosen before every instance quantifier, so it depends only on
`c`; this is the content of the O(·). The floors (Correction 1) are needed: as printed the bound
is `≤ 0` for `ε ∈ [(α+1)R, (α+2)R]` or `d = 0`, while for `T ≥ 2` at least one call is made.
The special cases state explicit constants 9/2 (stronger than O(·)). The expectation is over the
sampling of line 9 (`expectedRegret`, Reading 4); the call count is over rounds 1, …, T − 1
(`avgCalls`, Reading 3); N is the least admissible value at the current point (Reading 2); the
Ellipsoid method starts from B(0, 1) (Reading 1); the oracle, `s₁` and the optimal solutions of
Problem (5) are arbitrary (Reading 5). -/
theorem alg3_regret_and_oracle_complexity :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ c : ℝ, c₀ ≤ c → ∃ C : ℝ, 0 < C ∧
    ∀ {d : ℕ} (S : Setting d) (OK : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)),
      IsApproxOracle S OK →
      ∀ (sel : (N : ℕ) → EuclideanSpace ℝ (Fin d) → (Fin N → EuclideanSpace ℝ (Fin d)) → Fin N → ℝ),
      IsOptimalSelector sel →
      ∀ (s₁ : EuclideanSpace ℝ (Fin d)), s₁ ∈ S.K →
      ∀ (η ε : ℝ), 0 < η → 0 < ε → ε ≤ (S.α + 2) * S.R →
      ∀ (T : ℕ), 1 ≤ T →
      ∀ (f : ℕ → EuclideanSpace ℝ (Fin d)), (∀ t ∈ Finset.Icc 1 T, f t ∈ S.Fset) →
        (∀ t ∈ Finset.Icc 1 T, alg2Terminates S OK c ε (alg3Input S OK sel c s₁ η ε f t)) ∧
        expectedRegret S OK sel c s₁ η ε f T ≤
          S.α ^ 2 * S.R ^ 2 / ((T : ℝ) * η) + η * S.F ^ 2 / 2 + 3 * S.F * ε ∧
        avgCalls S OK sel c s₁ η ε f T ≤
          C * (1 + (η * S.α * S.R * S.F + η ^ 2 * S.F ^ 2) / ε ^ 2) * (max 1 (d : ℝ)) ^ 2 *
            max 1 (Real.log ((S.α + 1) * S.R / ε)) ∧
        (η = S.α * S.R * (T : ℝ) ^ (-(2 / 3 : ℝ)) / S.F →
          ε = S.α * S.R * (T : ℝ) ^ (-(1 / 3 : ℝ)) →
            expectedRegret S OK sel c s₁ η ε f T ≤
                9 / 2 * S.α * S.R * S.F * (T : ℝ) ^ (-(1 / 3 : ℝ)) ∧
              avgCalls S OK sel c s₁ η ε f T ≤
                C * (max 1 (d : ℝ)) ^ 2 * Real.log ((S.α + 1) * T / S.α)) ∧
        (η = S.α * S.R * (T : ℝ) ^ (-(1 / 2 : ℝ)) / S.F →
          ε = S.α * S.R * (T : ℝ) ^ (-(1 / 2 : ℝ)) →
            expectedRegret S OK sel c s₁ η ε f T ≤
                9 / 2 * S.α * S.R * S.F * (T : ℝ) ^ (-(1 / 2 : ℝ)) ∧
              avgCalls S OK sel c s₁ η ε f T ≤
                C * Real.sqrt T * (max 1 (d : ℝ)) ^ 2 * Real.log ((S.α + 1) * T / S.α)) := by sorry

end GarberOLO.Alg3
