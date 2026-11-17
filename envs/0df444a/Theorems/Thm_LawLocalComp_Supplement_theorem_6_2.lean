-- Prove2me | Theorems.Thm_LawLocalComp_Supplement_theorem_6_2
-- name    : LawLocalComp.Supplement.theorem_6_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T14:09:25.45182+00:00
-- url     : https://prove2.me/theorems/dc89af60-be96-4ea5-88f3-651d6071c52d
-- title:
--   Theorem 6.2 — joint coupling frontiers: CM order $\Theta(J(\varepsilon,N,q))$, forward-shortfall lower $\Omega(J(\varepsilon+Q\beta,N,q))$ and the forward upper (25)
-- statement:
--   **Setting.** Law-local maps, loads $L = \sum_j X_j a_j$ and $\tilde L = \sum_j Y_j a_j$ are as in Theorem 1.1. The supplied resources are a horizon $N$ and a rank promise $q$, $Q = \min\{N, q\}$, and
--   $$
--   J(\varepsilon, N, q) = \min\Bigl\{\sqrt{\tfrac{\log(N+1)\log(Q+1)}{\varepsilon}},\ \tfrac{\log(Q+1)}{\varepsilon}\Bigr\}.
--   $$
--   The **robust comparison** (14) for the maximum norm is $(1+\varepsilon)^{-1}\mathbb E\|L\|_\infty \le \mathbb E\|\tilde L\|_\infty \le (1+\varepsilon)\mathbb E\|L\|_\infty$; it allows arbitrary (biased, moving) outputs. For a coupling $\pi$ of input and output, the **forward shortfall** is $s_\pi = \mathbb E(X - \mathbb E_\pi[Y \mid X])_+$. Let $\operatorname{bits}(a/b) = 1 + \operatorname{size}(|a|) + \operatorname{size}(b)$ be the bit length of a rational number in lowest terms.
--
--   **Theorem.** For integers $N, q \ge 2$:
--
--   1. **CM upper ($0 < \varepsilon \le 1$).** Theorem 1.1's row-3 upper: a polynomial-time rational conditional-mean map preserving means and point masses, with $O(J(\varepsilon, N, q))$ atoms, satisfying (1) for all monotone norms under both resources.
--   2. **CM lower ($\varepsilon \le 2^{-40}$).** There are $c > 0$ and a polynomial $P$ such that, with $s = \lceil 1/\varepsilon\rceil + \operatorname{size}(N) + \operatorname{size}(q) + \operatorname{bits}(\varepsilon)$: every actual conditional-mean map satisfying (14) on all admitted selections of laws with descriptions of at most $P(s)$ bits has at least $c\,J(\varepsilon, N, q)$ positive output atoms on some rational law with a description of at most $P(s)$ bits.
--   3. **Forward-shortfall lower.** There are $c > 0$ and a polynomial $P$ such that for every rational $\beta \ge 0$ and rational $\varepsilon > 0$ with $\tau = \varepsilon + Q\beta \le 2^{-40}$, with $s$ as above plus $\operatorname{bits}(\beta)$: every map satisfying (14) in the same sense, whose input/output pairs (on every rational input) admit a coupling with $s_\pi \le \beta\,\mathbb E X$, has at least $c\,J(\tau, N, q)$ positive output atoms on some rational law with a description of at most $P(s)$ bits.
--   4. **Forward upper ($0 < \varepsilon \le 1$).** There are $C > 0$ and one map $\hat\Phi_{\varepsilon,N,q}$, polynomial-time in the input bits, $1/\varepsilon$, $\log N$ and $\log q$, whose output $\hat Y$ on every rational law $X$ is rational, has at most $C\,J(\varepsilon, N, q)$ atoms and satisfies $\mathbb E[\hat Y \mid X] = (1 + \varepsilon/4) X$ under some coupling, and such that for every admitted selection and every monotone norm $g$
--   $$
--   \mathbb E g(L) \le \mathbb E g(L_{\hat Y}) \le (1 + \varepsilon)\,\mathbb E g(L). \tag{25}
--   $$
--   5. **Exact branch.** Horizon one or rank one is exact by the mean (the mean map is a rational conditional-mean replacement and $\mathbb E g$ is unchanged).
--
--   Parts 3 at $\beta = 0$ and 4 together say that zero-forward-shortfall maps also have the sharp joint order. The theorem shows that the mixed order $J$ is not an artifact of the conditional-mean contraction: the opposite (forward) coupling has the same frontier.
--
--   **Formalization Note** Parts 1 and 5 are the published clauses `clauseU3` and `clauseE` of the goal. Uppers count all atoms, lowers positive atoms. Polynomial time is the published `PolyLawMap` with parameters $(\varepsilon, N, q)$ in binary and a unary pad of length $\lceil 1/\varepsilon\rceil$.
--
--   Differences from the source:
--
--   - encoding: finite nonnegative laws, rational inputs → finitely supported real laws on [0, ∞) (published Law) with the rationality predicate IsRatLaw; reason: base mission's published convention; same laws
--   - encoding: Θ(·), O(·), Ω(·) → absolute constants C > 0, c > 0 quantified existentially before every parameter; reason: standard reading of the asymptotic notation, as in the published goal
--   - encoding: Y = E[X | Λ], labels unordered and randomly split → published IsCondMean (a coupling with E[X | Y] = Y); reason: base mission's published convention
--   - encoding: the CM lower uses only maximum norms, i.e. (1) for g = ‖·‖∞ → the two-sided maximum-norm comparison (14) (published RobustContract); reason: for an actual conditional-mean map, conditional Jensen over the independent jobs gives E‖L̃‖∞ ≤ E‖L‖∞, so (14) and (1) for the maximum norm are the same condition
--   - encoding: s_π = E(X − E_π[Y | X])_+ for an input/output coupling π → AdmitsShortfall: Σ_x (x·P(X = x) − Σ_y y π(x, y))_+ ≤ β·E X for some coupling π; reason: the same quantity written without division by P(X = x)
--   - encoding: E[Ŷ | X] = (1 + ε/4)X → ScaledForward: a coupling with Σ_y y π(x, y) = (1 + ε/4)·x·P(X = x) for every x; reason: the same condition written without division
--   - reading: Upper construction and scalar witness/probe encodings are polynomial in input, 1/ε, logarithmic resources and accuracy bits; expanded copy lists need not be small → in parts 2 and 3 the comparison (14) is assumed only for selections whose every law has a description of ≤ P(s) bits (copy counts and dimension unrestricted), and the witness has ≤ P(s) bits; the uppers are PolyLawMap; reason: the probes and witness are the polynomial-size scalar laws; this reading implies the lower bounds with (14) assumed on all rational selections
--   - reading: any law-local map satisfying (14) whose input/output pairs admit s_π ≤ βEX → the shortfall bound is assumed for the output on every rational input; the map is otherwise arbitrary (real outputs, biased means, moving constants); reason: the literal reading of 'input/output pairs'
--   - reading: Thus zero-forward-shortfall maps also have the sharp joint order; No optimal β-dependent order or unrestricted biased-output sharpness is asserted → no separate conjunct; reason: the first sentence follows from part 3 at β = 0 and part 4; the second is a disclaimer
-- source:
--   Mahboub–Rahgoshay, Optimal Law-Local Compression for Stochastic Loads, STOC 2027 submission (manuscript of Oct. 29, 2026, sha256 5f71501c…aa873), Theorem 6.2, (25), p.10; (14), p.8; s_π, §6.1, p.10; proof pp.10–12

import Mathlib
import Definitions.Def_LawLocalComp_clauseU3
import Definitions.Def_LawLocalComp_clauseE
import Definitions.Def_LawLocalComp_RobustContract
import Definitions.Def_LawLocalComp_IsCondMean
import Definitions.Def_WeightedCongestionBR_bitLen
import Definitions.Def_LawLocalComp_Supplement_HasBits
import Definitions.Def_LawLocalComp_Supplement_AdmitsShortfall
import Definitions.Def_LawLocalComp_Supplement_ScaledForward
import Definitions.Def_LawLocalComp_Supplement_ForwardContract

namespace LawLocalComp

namespace Supplement

/-- **Theorem 6.2 (Joint coupling frontiers).**
Mahboub–Rahgoshay, *Optimal Law-Local Compression for Stochastic Loads*, STOC 2027
submission manuscript of Oct. 29, 2026 (sha256 5f71501c…aa873), Theorem 6.2, (25), p.10, with the robust comparison (14), p.8, and the shortfall
`s_π = E(X − E_π[Y | X])_+` of §6.1, p.10.

Five conjuncts, for integers `N, q ≥ 2` and `Q = min{N, q}`:
1. (CM upper) the published `clauseU3`: a polynomial-time rational conditional-mean map with
   `O(J(ε, N, q))` atoms satisfying (1), `0 < ε ≤ 1`;
2. (CM lower, `ε ≤ 2^{−40}`) every actual conditional-mean map satisfying (14) (maximum norm only)
   on selections of laws of bit length at most `P(s)` has at least `c J(ε, N, q)` positive output
   atoms on some rational input of bit length at most `P(s)`, `s = ⌈1/ε⌉ + size N + size q + bits ε`;
3. (forward-shortfall lower) for rational `β ≥ 0` with `τ = ε + Qβ ≤ 2^{−40}`, every map satisfying
   (14) in the same sense whose input/output pairs all admit `s_π ≤ β E X` has at least
   `c J(τ, N, q)` positive output atoms on some such input (`s` also counts `bits β`);
4. (forward upper, `0 < ε ≤ 1`) a polynomial-time rational map with `E[Ŷ | X] = (1 + ε/4) X`,
   `O(J(ε, N, q))` atoms and `E g(L) ≤ E g(L_Ŷ) ≤ (1 + ε) E g(L)` for all monotone norms (25);
5. (exact branch) the published `clauseE`: horizon or rank one is exact by the mean.

**Formalization Note.** Constants `c`, `C` and the polynomial `P` are existential and precede every
parameter. In conjuncts 2 and 3 the comparison (14) is assumed only for selections of laws of bit
length at most `P(s)` (copy counts and dimension unrestricted): the reading of "scalar witness/probe
encodings are polynomial …; expanded copy lists need not be small". In conjunct 3 the map is
otherwise arbitrary (real outputs, biased means, moving constants). -/
theorem theorem_6_2 :
    clauseU3 ∧
    (∃ c : ℝ, 0 < c ∧ ∃ P : Polynomial ℕ, ∀ N q : ℕ, 2 ≤ N → 2 ≤ q →
      ∀ ε : ℚ, 0 < ε → ε ≤ 1 / 2 ^ 40 →
      ∀ Φ : Law → Law, (∀ X : Law, IsRatLaw X → IsCondMean X (Φ X)) →
        RobustContract Φ (.both N q)
          (fun X => HasBits X (P.eval (⌈1 / ε⌉₊ + Nat.size N + Nat.size q + WeightedCongestionBR.bitLen ε))) (1 + ε) →
        ∃ X : Law, IsRatLaw X ∧
          HasBits X (P.eval (⌈1 / ε⌉₊ + Nat.size N + Nat.size q + WeightedCongestionBR.bitLen ε)) ∧
          c * Jfun ε N q ≤ (((Φ X).w.support.filter (fun y => 0 < y)).card : ℝ)) ∧
    (∃ c : ℝ, 0 < c ∧ ∃ P : Polynomial ℕ, ∀ N q : ℕ, 2 ≤ N → 2 ≤ q →
      ∀ ε β : ℚ, 0 < ε → 0 ≤ β → ε + (min N q : ℕ) * β ≤ 1 / 2 ^ 40 →
      ∀ Φ : Law → Law, (∀ X : Law, IsRatLaw X → AdmitsShortfall β X (Φ X)) →
        RobustContract Φ (.both N q)
          (fun X => HasBits X
            (P.eval (⌈1 / ε⌉₊ + Nat.size N + Nat.size q + WeightedCongestionBR.bitLen ε + WeightedCongestionBR.bitLen β))) (1 + ε) →
        ∃ X : Law, IsRatLaw X ∧
          HasBits X (P.eval (⌈1 / ε⌉₊ + Nat.size N + Nat.size q + WeightedCongestionBR.bitLen ε + WeightedCongestionBR.bitLen β)) ∧
          c * Jfun ((ε + (min N q : ℕ) * β : ℚ) : ℝ) N q ≤
            (((Φ X).w.support.filter (fun y => 0 < y)).card : ℝ)) ∧
    (∃ C : ℝ, 0 < C ∧ ∃ Φ : ℚ × ℕ × ℕ → Law → Law,
      PolyLawMap (fun p => [p.1, (p.2.1 : ℚ), (p.2.2 : ℚ)]) (fun p => ⌈1 / p.1⌉₊) (fun _ => True) Φ ∧
      ∀ ε : ℚ, 0 < ε → ε ≤ 1 → ∀ N q : ℕ, 2 ≤ N → 2 ≤ q →
        (∀ X : Law, IsRatLaw X → IsRatLaw (Φ (ε, N, q) X) ∧
          ScaledForward (1 + (ε : ℝ) / 4) X (Φ (ε, N, q) X) ∧
          ((Φ (ε, N, q) X).w.support.card : ℝ) ≤ C * Jfun ε N q) ∧
        ForwardContract (Φ (ε, N, q)) (.both N q) (1 + ε)) ∧
    clauseE := by sorry

end Supplement

end LawLocalComp
