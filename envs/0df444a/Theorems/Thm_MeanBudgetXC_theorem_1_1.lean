-- Prove2me | Theorems.Thm_MeanBudgetXC_theorem_1_1
-- name    : MeanBudgetXC.theorem_1_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T05:43:46.582094+00:00
-- url     : https://prove2.me/theorems/1bf9264b-5986-4596-8598-c26c2ce71724
-- title:
--   Theorem 1.1 — an exact mean-budget transition
-- statement:
--   Write $M=\binom N2$, and let $P^{(a)}_{N,d}$ and $P^{(a;B)}_{N,d}$ be the pair bodies of local laws on all contexts of size at most $d$ with at most $a$ ones, so that $P=P^{(2)}_{N,d}$ and $P_B=P^{(2;B)}_{N,d}$. Let $\mathrm{xc}$ be the extension complexity: the least number of inequalities in a lift, with equations and auxiliary variables free and real coefficients.
--
--   1. For every $3\le d\le N$ and $0<B\le2$,
--   $$M+1\le\mathrm{xc}(P_B)\le9M+5N+2.$$
--   The upper formulation has $6M+4N+1$ variables and, for rational $B$, coefficients of $O(\log N+\mathrm{bitlength}(B))$ bits.
--
--   2. Fix $\theta\in(0,1)$ and let $d=\lfloor\theta N\rfloor$. For all sufficiently large $N$,
--   $$\mathrm{xc}(P)=2^{\Theta_\theta(N)},\qquad\mathrm{xc}(P_B)=2^{\Theta_\theta(N)}\ \text{ for every }B>2.$$
--   The constants and the threshold on $N$ are independent of $B>2$, which may vary with $N$. These exponential bounds also hold if each local law permits at most $a$ ones, for every integer $a\ge2$, with constants uniform in $a$.
--
--   The theorem locates a sharp threshold: exact formulations have quadratic size up to mean budget two, and exponential size at fixed interior density for every positive surplus above it.
--
--   **Formalization Note** The upper bound in part 1 exhibits the formulation: $9M+5N+2$ inequalities in the $M$ pair coordinates and $5M+4N+1$ auxiliary variables, with no equations. The paper does not define bitlength; here it is the published size of a rational in lowest terms, $1+\mathrm{size}|a|+\mathrm{size}\,b$ for $a/b$.
--
--   Differences from the source:
--   - encoding: the vertex set is $[N]$ → `Fin N`; reason: same set up to the indexing from zero
--   - encoding: laws are given on contexts of size at most $d$ → the family is a function on all finite sets, with values on larger sets unconstrained; reason: the bodies are existential in the family and never read those values
--   - encoding: $\mathrm{xc}(P_B)\le9M+5N+2$, with $6M+4N+1$ variables → matrices with $9M+5N+2$ rows, $M$ output columns and $5M+4N+1$ auxiliary columns, with no equations, describing $P_B$; reason: the platform's `extensionComplexity` is an infimum in $\mathbb N$, so the formulation is exhibited; this implies the bound and is the formulation the coefficient clause speaks of
--   - reading: coefficients of $O(\log N+\mathrm{bitlength}(B))$ bits → one absolute constant $C$, chosen before $N,d,B$, bounds the bitlength of every coefficient and right-hand side by $C(\lfloor\log_2N\rfloor+\mathrm{bitlength}(B))$; reason: $\lfloor\log_2N\rfloor\ge1$ for $N\ge3$, so no additive constant is needed; the paper does not define bitlength, and the published `WeightedCongestionBR.bitLen` is used
--   - reading: $\mathrm{xc}=2^{\Theta_\theta(N)}$, with constants and threshold independent of $B$ and uniform in $a$ → constants $c_1,c_2>0$ and a threshold $N_0$ depending on $\theta$ only, chosen before $N$, $a$ and $B$, with $2^{c_1N}\le\mathrm{xc}$ and a formulation of size at most $2^{c_2N}$; reason: this is the quantifier order the paper states; $B$ may vary with $N$ because it is quantified after $N$
-- source:
--   Chao–Gao–Qi–Wang, A Sharp Mean-Budget Transition for Local Pair Marginals, STOC 2027 submission (manuscript sha256 882d9c71…), Theorem 1.1, p.4

import Mathlib
import Definitions.Def_ExtensionComplexity_TSP_extensionComplexity
import Definitions.Def_MeanBudgetXC_budgetBody
import Definitions.Def_WeightedCongestionBR_bitLen

namespace MeanBudgetXC

open Matrix ExtensionComplexity.TSP

/-- **Theorem 1.1** (An exact mean-budget transition) (Chao–Gao–Qi–Wang, *A Sharp Mean-Budget
Transition for Local Pair Marginals*, STOC 2027 submission, manuscript sha256 882d9c71…9e76,
Theorem 1.1, p.4). Write `M = (N choose 2)`.
1. For every `3 ≤ d ≤ N` and `0 < B ≤ 2`, `M + 1 ≤ xc(P_B) ≤ 9M + 5N + 2`. The upper formulation
   has `6M + 4N + 1` variables and, for rational `B`, coefficients of `O(log N + bitlength(B))`
   bits.
2. Fix `θ ∈ (0, 1)` and let `d = ⌊θN⌋`. For all sufficiently large `N`, `xc(P) = 2^{Θ_θ(N)}` and
   `xc(P_B) = 2^{Θ_θ(N)}` for every `B > 2`. The constants and the threshold on `N` are
   independent of `B > 2`, which may vary with `N`. These exponential bounds also hold if each
   local law permits at most `a` ones, for every integer `a ≥ 2`, with constants uniform in `a`.

**Formalization Note** The vertex set is `Fin N`; `P_B = budgetBody (Fin N) d 2 B` and
`P^{(a)} = pairBody (Fin N) d a`, `P^{(a;B)} = budgetBody (Fin N) d a B`. Extension complexity is
the platform's `extensionComplexity` (inequalities counted, equations and auxiliary variables
free). Every upper bound is stated as the existence of a formulation, never as a bound on the
infimum. In part 1 the formulation is exhibited: `9M + 5N + 2` inequalities in the `M` pair
coordinates and `5M + 4N + 1` auxiliary variables (`6M + 4N + 1` variables in all), no equations;
`O(log N + bitlength(B))` is read with one absolute constant `C`, chosen before `N, d, B`, applied
to every coefficient and right-hand side (`log N` is `Nat.log 2 N ≥ 1` for `N ≥ 3`); `bitlength`,
which the paper does not define, is the published `WeightedCongestionBR.bitLen`
(`1 + size |numerator| + size denominator`, in lowest terms). In part 2,
`2^{Θ_θ(N)}` is read as constants `0 < c₁, c₂` and a threshold `N₀` depending on `θ` only, chosen
before `N`, `a` and `B`. -/
theorem theorem_1_1 :
    (∃ C : ℕ, ∀ N d : ℕ, 3 ≤ d → d ≤ N → ∀ B : ℝ, 0 < B → B ≤ 2 →
      N.choose 2 + 1 ≤ extensionComplexity (budgetBody (Fin N) d 2 B) ∧
        ∃ (Ele : Matrix (Fin (9 * N.choose 2 + 5 * N + 2)) (Pair (Fin N)) ℝ)
          (Fle : Matrix (Fin (9 * N.choose 2 + 5 * N + 2)) (Fin (5 * N.choose 2 + 4 * N + 1)) ℝ)
          (g : Fin (9 * N.choose 2 + 5 * N + 2) → ℝ),
          (∀ q : Pair (Fin N) → ℝ,
            q ∈ budgetBody (Fin N) d 2 B ↔ ∃ y, Ele *ᵥ q + Fle *ᵥ y ≤ g) ∧
          ∀ β : ℚ, (β : ℝ) = B →
            (∀ k e, ∃ ρ : ℚ, (ρ : ℝ) = Ele k e ∧
              WeightedCongestionBR.bitLen ρ ≤ C * (Nat.log 2 N + WeightedCongestionBR.bitLen β)) ∧
            (∀ k l, ∃ ρ : ℚ, (ρ : ℝ) = Fle k l ∧
              WeightedCongestionBR.bitLen ρ ≤ C * (Nat.log 2 N + WeightedCongestionBR.bitLen β)) ∧
            ∀ k, ∃ ρ : ℚ, (ρ : ℝ) = g k ∧
              WeightedCongestionBR.bitLen ρ ≤ C * (Nat.log 2 N + WeightedCongestionBR.bitLen β)) ∧
    ∀ θ : ℝ, 0 < θ → θ < 1 → ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ a : ℕ, 2 ≤ a →
      ((2 : ℝ) ^ (c₁ * N) ≤ extensionComplexity (pairBody (Fin N) ⌊θ * N⌋₊ a) ∧
        ∃ r : ℕ, IsEFOfSize (pairBody (Fin N) ⌊θ * N⌋₊ a) r ∧ (r : ℝ) ≤ (2 : ℝ) ^ (c₂ * N)) ∧
      ∀ B : ℝ, 2 < B →
        (2 : ℝ) ^ (c₁ * N) ≤ extensionComplexity (budgetBody (Fin N) ⌊θ * N⌋₊ a B) ∧
          ∃ r : ℕ, IsEFOfSize (budgetBody (Fin N) ⌊θ * N⌋₊ a B) r ∧
            (r : ℝ) ≤ (2 : ℝ) ^ (c₂ * N) := by sorry

end MeanBudgetXC
