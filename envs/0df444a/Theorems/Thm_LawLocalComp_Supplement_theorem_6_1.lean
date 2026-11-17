-- Prove2me | Theorems.Thm_LawLocalComp_Supplement_theorem_6_1
-- name    : LawLocalComp.Supplement.theorem_6_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T14:08:10.886428+00:00
-- url     : https://prove2.me/theorems/f2c76224-355f-4a16-ac64-500ccde63cd3
-- title:
--   Theorem 6.1 — wider-domain rank two: order $\Theta(\min\{\sqrt{\log(N+1)/\varepsilon}, 1/\varepsilon\})$ for $\varepsilon \le 1/16384$, and (22) from one norm and two directions
-- statement:
--   **Setting.** A law-local map $\Phi$ sends each finite nonnegative law $X$ to an output law $Y = \Phi(X)$; identical laws get the same output law, sampled independently per copy. For independent jobs $X_j$ with directions $a_j \in \mathbb R^d_+$ and a norm $g$ monotone on $\mathbb R^d_+$, write $L = \sum_j X_j a_j$ and $\tilde L = \sum_j Y_j a_j$. The contracting guarantee (1) is
--   $$
--   \mathbb E g(\tilde L) \le \mathbb E g(L) \le (1 + \varepsilon)\,\mathbb E g(\tilde L).
--   $$
--   Here the selection is limited by a **horizon** $N$ (at most $N$ jobs) and **rank two** ($\dim \operatorname{span}\{a_j\} \le 2$). A map is an **actual conditional-mean map** if every output is $Y = \mathbb E[X \mid \Lambda]$ for some (possibly randomized) labelling $\Lambda$.
--
--   **Theorem.** Natural logarithms throughout.
--
--   1. **Upper ($0 < \varepsilon \le 1$).** There are $C > 0$ and one map $\Phi_{\varepsilon, N}$, computable in time polynomial in the input bits, $1/\varepsilon$ and $\log N$, such that for every rational $\varepsilon \in (0, 1]$ and every $N \ge 2$: on every rational law $X$ the output is a rational conditional-mean replacement of $X$ preserving the mean and point masses, with at most
--   $$
--   C \min\Bigl\{\sqrt{\tfrac{\log(N+1)}{\varepsilon}},\ \tfrac1\varepsilon\Bigr\}
--   $$
--   atoms, and $\Phi_{\varepsilon,N}$ satisfies (1) for every selection of horizon $N$ and rank two and every monotone norm.
--   2. **Lower ($\varepsilon \le 1/16384$).** There are $c > 0$ and one polynomial $P$ such that for every $N \ge 2$, every rational $0 < \varepsilon \le 1/16384$ and every actual conditional-mean map $\Phi$ satisfying (1) under horizon $N$ and rank two, some rational law $X$ with a description of at most $P(\lceil 1/\varepsilon\rceil + \operatorname{size}(N) + \operatorname{bits}(\varepsilon))$ bits has
--   $$
--   |\operatorname{supp}(\Phi(X)) \setminus \{0\}| \ge c \min\Bigl\{\sqrt{\tfrac{\log(N+1)}{\varepsilon}},\ \tfrac1\varepsilon\Bigr\}.
--   $$
--   3. **One norm and two directions, (22).** There are one norm $g$ on $\mathbb R^2$ monotone on $\mathbb R^2_+$, two directions $a_1, a_2 \in \mathbb R^2_+$ and one polynomial $P$ such that for every $N \ge 5$, every rational $0 < \varepsilon \le 1/1024$ and every actual conditional-mean map $\Phi$ satisfying (1) for this $g$ on all selections of at most $N$ jobs with directions in $\{a_1, a_2\}$, some rational law $X$ with a description of at most $P(\lceil 1/\varepsilon\rceil + \operatorname{size}(N) + \operatorname{bits}(\varepsilon))$ bits ($\operatorname{size}(N)$ the binary length of $N$, $\operatorname{bits}(\varepsilon)$ that of the rational $\varepsilon$) has
--   $$
--   |\operatorname{supp}(\Phi(X)) \setminus \{0\}| \ge 2^{-14} \min\Bigl\{\sqrt{H/\varepsilon},\ 1/\varepsilon\Bigr\}, \qquad H = \lfloor \log_4(N - 1) \rfloor. \tag{22}
--   $$
--
--   The theorem extends the rank-two case of Theorem 1.1's mixed lower bound from $\varepsilon \le 2^{-40}$ to $\varepsilon \le 1/16384$, and shows that the lower bound is forced already by a single fixed monotone norm and two directions, with a witness of polynomial description.
--
--   **Formalization Note** The upper map's parameters $(\varepsilon, N)$ are written in binary with a unary pad of length $\lceil 1/\varepsilon\rceil$ (published `PolyLawMap`); horizon $N$ with rank two is the resource `both N 2`. Uppers count all output atoms, lowers positive atoms, which is $|\operatorname{supp} Y \setminus \{0\}|$ since laws are nonnegative. $\lfloor\log_4(N-1)\rfloor$ is `Nat.log 4 (N - 1)`.
--
--   Differences from the source:
--
--   - encoding: finite nonnegative laws, rational inputs → finitely supported real laws on [0, ∞) (published Law) with the rationality predicate IsRatLaw; reason: base mission's published convention; same laws
--   - encoding: Θ(·), O(·), Ω(·) → absolute constants C > 0, c > 0 quantified existentially before every parameter; reason: standard reading of the asymptotic notation, as in the published goal
--   - encoding: horizon N, rank two → the published resource Resource.both N 2; reason: same admitted selections
--   - encoding: Y = E[X | Λ], labels unordered and randomly split → published IsCondMean (a coupling with E[X | Y] = Y); reason: base mission's published convention; equivalent to conditioning on a randomized label
--   - reading: The upper of Theorem 1.1 holds for ε ≤ 1 → the full upper of Theorem 1.1 (polynomial time, rational conditional-mean outputs preserving means and point masses, guarantee (1)) at horizon N and rank two with the printed order min{√(log(N+1)/ε), 1/ε}; reason: the sentence imports Theorem 1.1's upper; the order is the theorem's own Θ order (equal to J(ε, N, 2) up to the constant log 3)
--   - reading: One fixed monotone norm and two directions suffice → in (22) the hypothesis is (1) for one norm g and directions in {a₁, a₂} on at most N jobs, with g, a₁, a₂ existential and fixed before N, ε and the map; reason: the proof's norm h(|x₁|, |x₂|) serves N ≥ 5; for N = 2, 3, 4 the paper switches to the max-norm two-job argument, so the claim attaches to (22)
--   - reading: witness description is polynomial in 1/ε, log N and accuracy bits → in the Θ lower (part 2) and in (22) (part 3) the witness has a list representation of bit length ≤ P(⌈1/ε⌉ + size N + bits ε) for one polynomial P fixed before the parameters; reason: the natural reading of 'polynomial description'; the sentence names log N and so governs every lower of the theorem (the stronger reading); the N ≥ 5 witnesses of (17)/(22) and the uniform-midpoint witnesses for N = 2, 3, 4 (p.8) are polynomial-size rational laws
-- source:
--   Mahboub–Rahgoshay, Optimal Law-Local Compression for Stochastic Loads, STOC 2027 submission (manuscript of Oct. 29, 2026, sha256 5f71501c…aa873), Theorem 6.1, (22), p.9; model §1, (1), p.2

import Mathlib
import Definitions.Def_LawLocalComp_IsGoodOutput
import Definitions.Def_LawLocalComp_Contract
import Definitions.Def_LawLocalComp_PolyLawMap
import Definitions.Def_LawLocalComp_IsMonotoneNorm
import Definitions.Def_WeightedCongestionBR_bitLen
import Definitions.Def_LawLocalComp_Supplement_HasBits
import Definitions.Def_LawLocalComp_Supplement_NormContract2

namespace LawLocalComp

namespace Supplement

/-- **Theorem 6.1 (Wider-domain rank two).**
Mahboub–Rahgoshay, *Optimal Law-Local Compression for Stochastic Loads*, STOC 2027
submission manuscript of Oct. 29, 2026 (sha256 5f71501c…aa873), Theorem 6.1, (22), p.9, with the model of §1, p.2 ((1)) and §6, p.9 ("Here Y = E[X | Λ];
labels may be unordered and randomly split").

Three conjuncts:
1. (upper, `0 < ε ≤ 1`) one polynomial-time parametrized map whose output on every rational law is
   a rational conditional-mean replacement preserving the mean and point masses, with at most
   `C min{√(log(N + 1)/ε), 1/ε}` atoms, satisfying (1) under horizon `N ≥ 2` and rank two;
2. (lower, `ε ≤ 1/16384`) every actual conditional-mean map satisfying (1) under horizon `N ≥ 2`
   and rank two has at least `c min{√(log(N + 1)/ε), 1/ε}` positive output atoms on some rational
   input of bit length at most `P(⌈1/ε⌉ + size N + bits ε)`, for one polynomial `P` fixed before
   the parameters;
3. ((22)) there are one monotone norm `g` on `ℝ²`, two directions `a₁, a₂ ∈ ℝ²_+` and one polynomial
   `P` such that for `N ≥ 5`, `0 < ε ≤ 1/1024` and every actual conditional-mean map satisfying (1)
   for `g` and directions in `{a₁, a₂}` with at most `N` jobs, some rational input of bit length at
   most `P(⌈1/ε⌉ + size N + bits ε)` has at least `2^{−14} min{√(H/ε), 1/ε}` positive output atoms,
   `H = ⌊log₄(N − 1)⌋`.

**Formalization Note.** `O`/`Ω` constants are existential and placed before every parameter; the
norm, the directions and the polynomial in (22) are fixed before `N`, `ε` and the map. Natural
logarithms. Uppers count all output atoms, lowers count positive ones. -/
theorem theorem_6_1 :
    (∃ C : ℝ, 0 < C ∧ ∃ Φ : ℚ × ℕ → Law → Law,
      PolyLawMap (fun p => [p.1, (p.2 : ℚ)]) (fun p => ⌈1 / p.1⌉₊) (fun _ => True) Φ ∧
      ∀ ε : ℚ, 0 < ε → ε ≤ 1 → ∀ N : ℕ, 2 ≤ N →
        (∀ X : Law, IsRatLaw X → IsGoodOutput X (Φ (ε, N) X) ∧
          ((Φ (ε, N) X).w.support.card : ℝ) ≤
            C * min (Real.sqrt (Real.log ((N : ℝ) + 1) / ε)) (1 / ε)) ∧
        Contract (Φ (ε, N)) (.both N 2) (fun _ => True) (1 + ε)) ∧
    (∃ c : ℝ, 0 < c ∧ ∃ P : Polynomial ℕ, ∀ N : ℕ, 2 ≤ N → ∀ ε : ℚ, 0 < ε → ε ≤ 1 / 16384 →
      ∀ Φ : Law → Law, (∀ X : Law, IsRatLaw X → IsCondMean X (Φ X)) →
        Contract Φ (.both N 2) (fun _ => True) (1 + ε) →
        ∃ X : Law, IsRatLaw X ∧ HasBits X (P.eval (⌈1 / ε⌉₊ + Nat.size N + WeightedCongestionBR.bitLen ε)) ∧
          c * min (Real.sqrt (Real.log ((N : ℝ) + 1) / ε)) (1 / ε) ≤
            (((Φ X).w.support.filter (fun y => 0 < y)).card : ℝ)) ∧
    (∃ g : (Fin 2 → ℝ) → ℝ, IsMonotoneNorm g ∧ ∃ a₁ a₂ : Fin 2 → ℝ, 0 ≤ a₁ ∧ 0 ≤ a₂ ∧
      ∃ P : Polynomial ℕ, ∀ N : ℕ, 5 ≤ N → ∀ ε : ℚ, 0 < ε → ε ≤ 1 / 1024 →
        ∀ Φ : Law → Law, (∀ X : Law, IsRatLaw X → IsCondMean X (Φ X)) →
          NormContract2 Φ g a₁ a₂ N (1 + ε) →
          ∃ X : Law, IsRatLaw X ∧ HasBits X (P.eval (⌈1 / ε⌉₊ + Nat.size N + WeightedCongestionBR.bitLen ε)) ∧
            (1 / 2 ^ 14 : ℝ) * min (Real.sqrt ((Nat.log 4 (N - 1) : ℝ) / ε)) (1 / ε) ≤
              (((Φ X).w.support.filter (fun y => 0 < y)).card : ℝ)) := by sorry

end Supplement

end LawLocalComp
