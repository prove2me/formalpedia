-- Prove2me | Theorems.Thm_LawLocalComp_Supplement_theorem_9_3
-- name    : LawLocalComp.Supplement.theorem_9_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T14:11:14.582261+00:00
-- url     : https://prove2.me/theorems/bcd7a94a-0e13-43e2-9102-c976e40bd5c6
-- title:
--   Theorem 9.3 — sharp envelope accuracy: $\Theta_{\alpha,A}(\min\{\sqrt{U L_U/\varepsilon}, L_U/\varepsilon\})$ atoms for activity-normalized sub-Weibull laws
-- statement:
--   **Setting.** Law-local maps, the guarantee (1) and the robust maximum-norm comparison (14) are as in Theorem 1.1. Fix rational $\alpha > 0$ and $A \ge 1$, and consider the **activity-normalized sub-Weibull class** of Definition 9.1: point masses, and nonconstant laws $X$ with $b = \min\operatorname{supp} X$, $R = X - b$, $\nu = \mathbb E[R \mid R > 0]$ and $P(R \ge A\nu u \mid R > 0) \le 2^{-u^\alpha}$ for $u \ge 1$. Let $M = N$, $q$ or $\min\{N, q\}$ according to the supplied resources (horizon $N$, rank $q$, or both), and put $U = \ln(M + 1)$, $L_U = \ln(2 + U)$.
--
--   **Theorem.**
--
--   1. **Upper.** For every rational $\alpha > 0$ and $A \ge 1$ there are $C > 0$ and one map $\Phi_{\varepsilon, R}$, computable in time polynomial in the input bits, $1/\varepsilon$ and $\log M$ (the degree may depend on $\alpha$ and $A$), such that for every rational $0 < \varepsilon \le 1$ and every supplied resource with $M \ge 2$: on every rational law $X$ of the class the output is a rational conditional-mean replacement of $X$ preserving the mean and point masses with at most
--   $$
--   C \min\Bigl\{\sqrt{\tfrac{U\,L_U}{\varepsilon}},\ \tfrac{L_U}{\varepsilon}\Bigr\} \tag{45}
--   $$
--   atoms, and (1) holds for every admitted selection of rational laws of the class and every monotone norm.
--   2. **Lower.** For every rational $\alpha > 0$ and $A \ge 2$ there is $c > 0$ such that for every supplied resource with $M \ge 2$, every rational $0 < \varepsilon \le 2^{-32}$ and every map satisfying (14) on the admitted selections of rational laws of the class (outputs arbitrary: biased means and moving constants allowed), some rational law of the class has at least $c \min\{\sqrt{U L_U/\varepsilon}, L_U/\varepsilon\}$ positive output atoms.
--   3. **Exact branches.** Rank or horizon one is exact by the mean, and point masses have exact mean replacements.
--
--   Compared with Theorem 1.1's lattice-log-concave row, a tail envelope alone yields the order (45), not the faster $A(\varepsilon, M)$: fixed tail decay does not provide the hazard-rate accuracy gain.
--
--   **Formalization Note** The class is `IsSubWeibull α A`; its conditional tail bound is written multiplied by the activity $p = P(R > 0)$. The constants $C$, $c$ and the machine are quantified after $\alpha$ and $A$ and before every other parameter. Part 3 is the published clause `clauseE`.
--
--   Differences from the source:
--
--   - encoding: finite nonnegative laws, rational inputs → finitely supported real laws on [0, ∞) (published Law) with the rationality predicate IsRatLaw; reason: base mission's published convention; same laws
--   - encoding: O_{α,A}(·), Ω(·) for fixed α, A → constants C > 0, c > 0 and the machine quantified after ∀ α A and before every other parameter; reason: the printed subscripts; 'The polynomial degree may depend on the fixed class constants'
--   - encoding: M = N, q, or min{N, q} according to the supplied resources → the published Resource and Resource.M; the machine receives the resource in binary (Resource.params); reason: base mission's published convention
--   - encoding: P(R ≥ Aνu | R > 0) ≤ 2^{−u^α} → P(X − b ≥ Aνu) ≤ 2^{−u^α}·P(X > b) (Definition 9.1 as IsSubWeibull); reason: Aνu > 0 for nonconstant X, so the event lies in {R > 0}
--   - reading: (1) and the robust comparison (14) for the class → the contracts range over selections of rational class members only; reason: the class is the theorem's hypothesis on the inputs; for the lower this is the strongest reading, as in the published goal's lattice row
--   - encoding: Rank/horizon one and point masses have exact mean replacements → the published clauseE (the mean map is a rational conditional-mean replacement preserving means and point masses, and exact for one job or rank one); reason: same content, stated for all rational laws
-- source:
--   Mahboub–Rahgoshay, Optimal Law-Local Compression for Stochastic Loads, STOC 2027 submission (manuscript of Oct. 29, 2026, sha256 5f71501c…aa873), Theorem 9.3, (45), p.16; Definition 9.1, (44), p.16; (1), p.2; (14), p.8

import Mathlib
import Definitions.Def_LawLocalComp_IsGoodOutput
import Definitions.Def_LawLocalComp_Contract
import Definitions.Def_LawLocalComp_RobustContract
import Definitions.Def_LawLocalComp_PolyLawMap
import Definitions.Def_LawLocalComp_Resource_M
import Definitions.Def_LawLocalComp_Resource_params
import Definitions.Def_LawLocalComp_clauseE
import Definitions.Def_LawLocalComp_Supplement_IsSubWeibull
import Definitions.Def_LawLocalComp_Supplement_envOrder

namespace LawLocalComp

namespace Supplement

/-- **Theorem 9.3 (Sharp envelope accuracy).**
Mahboub–Rahgoshay, *Optimal Law-Local Compression for Stochastic Loads*, STOC 2027
submission manuscript of Oct. 29, 2026 (sha256 5f71501c…aa873), Theorem 9.3, (45), p.16, for the class of Definition 9.1, (44), p.16, with (1), p.2 and (14),
p.8.

Three conjuncts, with `M = N`, `q` or `min{N, q}` for the supplied resource `R`, `U = ln(M + 1)` and
`LU = ln(2 + U)`:
1. (upper) for every rational `α > 0` and `A ≥ 1` there are `C > 0` and one polynomial-time map
   (degree depending on `α, A`) whose output on every rational sub-Weibull law is a rational
   conditional-mean replacement preserving the mean and point masses with at most
   `C min{√(U·LU/ε), LU/ε}` atoms, and which satisfies (1) on selections of such laws, for every
   `0 < ε ≤ 1` and every resource with `M ≥ 2`;
2. (lower) for `α > 0` and `A ≥ 2` there is `c > 0` such that for every resource with `M ≥ 2`
   and `0 < ε ≤ 2^{−32}`, every map satisfying (14) on selections of rational sub-Weibull laws has at
   least `c min{√(U·LU/ε), LU/ε}` positive output atoms on some rational sub-Weibull input;
3. (exact branches) the published `clauseE`: rank or horizon one is exact by the mean, and point
   masses are preserved.

**Formalization Note.** `O_{α,A}` constants come after `∀ α A` and before every other parameter. The
contracts range over class members only. -/
theorem theorem_9_3 :
    (∀ α A : ℚ, 0 < α → 1 ≤ A → ∃ C : ℝ, 0 < C ∧ ∃ Φ : ℚ × Resource → Law → Law,
      PolyLawMap (fun p => p.1 :: p.2.params) (fun p => ⌈1 / p.1⌉₊) (IsSubWeibull α A) Φ ∧
      ∀ ε : ℚ, 0 < ε → ε ≤ 1 → ∀ R : Resource, 2 ≤ R.M →
        (∀ X : Law, IsRatLaw X → IsSubWeibull α A X → IsGoodOutput X (Φ (ε, R) X) ∧
          ((Φ (ε, R) X).w.support.card : ℝ) ≤ C * envOrder ε R.M) ∧
        Contract (Φ (ε, R)) R (IsSubWeibull α A) (1 + ε)) ∧
    (∀ α A : ℚ, 0 < α → 2 ≤ A → ∃ c : ℝ, 0 < c ∧ ∀ R : Resource, 2 ≤ R.M →
      ∀ ε : ℚ, 0 < ε → ε ≤ 1 / 2 ^ 32 →
      ∀ Φ : Law → Law, RobustContract Φ R (IsSubWeibull α A) (1 + ε) →
        ∃ X : Law, IsRatLaw X ∧ IsSubWeibull α A X ∧
          c * envOrder ε R.M ≤ (((Φ X).w.support.filter (fun y => 0 < y)).card : ℝ)) ∧
    clauseE := by sorry

end Supplement

end LawLocalComp
