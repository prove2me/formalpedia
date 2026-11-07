-- Prove2me | Theorems.Thm_FriedgutCoalition_corollary_3_2
-- name    : FriedgutCoalition.corollary_3_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:34:23.908875+00:00
-- url     : https://prove2.me/theorems/bb68c42d-c2a6-490e-91a0-5f9756184fd4
-- title:
--   Corollary 3.2 — every monotone or Borel $f:[0,1]^n\to\{0,1\}$ has a coalition of $O_\varepsilon(n/\sqrt{\log n})$ coordinates forcing some output
-- statement:
--   For every $\varepsilon>0$ there is a constant $C=C(\varepsilon)>0$ such that the following holds. For every $n\in\mathbb N$, equip $[0,1]^n$ with the uniform measure, and let $f:[0,1]^n\to\{0,1\}$ be monotone or Borel measurable. Then there are $b\in\{0,1\}$ and $B\subseteq[n]$ with
--
--   $$|B|\le C\cdot\frac{n}{\sqrt{\log n}}\qquad\text{and}\qquad\mathbf P^b_B(f)\ge1-\varepsilon.$$
--
--   Here $\mathbf P^b_B(f)$ is the probability, over a uniform $x\in[0,1]^n$, that the coalition $B$ can choose values for its coordinates, after seeing the others, that make $f$ output $b$. Logarithms are base $2$.
--
--   This resolves Friedgut's conjecture on influential coalitions for the solid cube: the constant depends only on $\varepsilon$, and the target $b$ must be allowed to depend on $f$.
--
--   Differences from the source:
--   - encoding: |B| ≤ C · n/√log(n) → |B| · √(log₂ n) ≤ C · n; reason: the same inequality for n ≥ 2; at n = 1 the printed bound divides by zero and the Lean form puts no bound on |B| (Lean's x/0 = 0 would instead force |B| ≤ 0, which is false); logarithms are base 2 (p.4)
--   - encoding: P^b_S(f) on [0,1]ⁿ, the probability of the success event → cubeCoalProb: 1 minus the outer measure of the failure set (the inner measure of the success event); reason: equal to the source's value whenever the success event is Lebesgue measurable, which p.5 proves for monotone and Borel f; never larger, so lower bounds are not weakened
--   - encoding: Borel measurable → Measurable f for the product σ-algebra on Fin n → unitInterval (the Borel σ-algebra) and the discrete σ-algebra on Bool; reason: Lean convention; the same functions
--   - encoding: {0,1}, [n], [r] = {1,…,r} → Bool (false < true), Fin n, Fin r (the value 1 of [r] is 0 : Fin r, the value r is its top); reason: Lean conventions; the same instances
-- source:
--   Chattopadhyay, Gurumukhani, A Resolution of Friedgut's Conjecture on Influential Coalitions, arXiv:2609.16401 (held file sha256 51f298ff…), Corollary 3.2, p.8

import Mathlib
import Definitions.Def_FriedgutCoalition_cubeCoalProb

namespace FriedgutCoalition

/-- **Corollary 3.2** (E. Chattopadhyay, M. Gurumukhani, *A Resolution of Friedgut's Conjecture on
Influential Coalitions*, arXiv:2609.16401 (held file sha256 51f298ff…), p.8). For every `ε > 0` there is `C = C(ε) > 0` such that for every
`n` and every monotone or Borel measurable `f : [0,1]ⁿ → {0,1}` there are `b ∈ {0,1}` and
`B ⊆ [n]` with `|B| ≤ C · n / √(log n)` and `P^b_B(f) ≥ 1 − ε`.

**Formalization Note.**
* `|B| ≤ C · n / √(log₂ n)` is written `|B| · √(log₂ n) ≤ C · n`: the same for `n ≥ 2`; at `n = 1`
  the printed bound divides by zero and the Lean form puts no bound on `|B|` (at `n = 0`, `B = ∅`).
  Logarithms are base 2 (p.4).
* `C` is chosen before `n` and `f`; `b` and `B` depend on `f`.
* `P^b_B(f)` is `cubeCoalProb`: the inner measure of the success event, with the coalition choosing its
  values after the other coordinates are drawn.
* "Borel measurable" is `Measurable f` for the product (= Borel) σ-algebra on `Fin n → unitInterval`
  and the discrete σ-algebra on `Bool`. The hypothesis is the disjunction `Monotone f ∨ Measurable f`. -/
theorem corollary_3_2 : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
    ∀ (n : ℕ) (f : (Fin n → unitInterval) → Bool), (Monotone f ∨ Measurable f) →
      ∃ (b : Bool) (B : Finset (Fin n)),
        (B.card : ℝ) * Real.sqrt (Real.logb 2 n) ≤ C * n ∧ 1 - ε ≤ cubeCoalProb f B b := by sorry

end FriedgutCoalition
