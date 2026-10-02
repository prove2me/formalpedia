-- Prove2me | Theorems.Thm_MDPFinance_PDMDP_theorem_8_3_1
-- name    : MDPFinance.PDMDP.theorem_8_3_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-27T23:07:35.344566+00:00
-- url     : https://prove2.me/theorems/ff9f63ee-5171-42d3-a3c3-22c20dc6fdfd
-- title:
--   Theorem 8.3.1 — fixed-point equation and optimal policy, infinite-horizon chain
-- statement:
--   Specializing Theorems 8.2.6-8.2.7 to the continuous-time Markov Decision Chain (uncontrolled flow, so the "uncontrolled flow" branch of Theorem 8.2.7 always applies), this theorem gives the chain's own fixed-point equation directly: $\beta V_\infty(x) = \sup_{u\in U}\big[r(x,u)+\sum_{y\in E}q_{xy}(u)V_\infty(y)\big]$ — literally the Hamilton–Jacobi–Bellman equation for this discrete-state chain — under compactness of $U$ and continuity/upper-semicontinuity of the rate function, the bounding-function sum, and the reward. An optimal stationary Markov policy exists, built from any decision rule achieving the pointwise supremum.
--
--   **Formalization Note.** $V_\infty$ is realized operationally as the chain's own embedded discrete-time value function `Ch.Vinf`, matching the `theorem_8_2_7`-style convention: the book's own proof identifies the two via Theorem 8.2.1's correspondence (here specialized to trivial flow), so no separate continuous-time process construction is needed to *state* this fixed-point/optimal-policy conclusion.
--
--   **Moderation note.** The draft's chain theorem carried no contraction condition, no measurability, real `tsum`s (junk `0` on divergent series) and a fixed-point equation for an arbitrary function. Now with `E` having measurable singletons, `U` a compact Borel space, an upper bounding function for the chain with `c_Q λ/(β+λ) < 1`, `y ↦ ∑_y Q(y|x,u) b(y)` continuous in `u` and `r`, `q` continuous in `u`: `V_∞ ∈ IB_b^+`, the fixed-point equation `β V_∞(x) = sup_u { r(x,u) + λ(x,u) [∫ V_∞ dQ(·|x,u) − V_∞(x)] }` in `[-∞,∞]`, and a measurable maximizer `f^*` with `J_{(f^*)^∞} = V_∞`.
-- source:
--   Bäuerle and Rieder, Markov Decision Processes with Applications to Finance, Universitext, Springer 2011, DOI 10.1007/978-3-642-18324-9, p. 257, PDF 268, Theorem 8.3.1

import Mathlib
import Definitions.Def_MDPFinance_PDMDP_Chain

open MeasureTheory Filter

namespace MDPFinance.PDMDP

variable {E U : Type*} [MeasurableSpace E] [Countable E] [MeasurableSingletonClass E]
  [MeasurableSpace U] [TopologicalSpace U] [BorelSpace U] [TopologicalSpace.MetrizableSpace U]
  [SecondCountableTopology U] [StandardBorelSpace U]

/-- Theorem 8.3.1 (Bäuerle–Rieder, p. 257, PDF 268). Suppose the continuous-time Markov Decision
Chain has an upper bounding function `b` with `α_b < 1` (`c_Q λ/(β+λ) < 1`, the book's bound
`α_b ≤ c_Q λ/(β+λ)`) and (i) `U` compact, (ii) `u ↦ q_{xy}(u)` continuous, (iii) `u ↦ Σ_y b(y)
q_{xy}(u)` continuous (rendered through `Σ_y b(y) Q({y}|x,u) = b(x) + λ^{-1} Σ_y b(y) q_{xy}(u)`),
(iv) `u ↦ r(x,u)` upper semicontinuous. Then a) `V_∞ ∈ IB_b^+` and `V_∞` is a fixed point of
`T`, i.e. `β V_∞(x) = sup_{u∈U} [r(x,u) + Σ_y q_{xy}(u) V_∞(y)]` (with `Σ_y q_{xy}(u) V_∞(y) =
λ(∫ V_∞ dQ(·|x,u) - V_∞(x))`); b) there is an optimal stationary Markov policy `π^*_t = f^*(X_{t-})`
for a measurable `f^* : E → U`, `f^*(x)` a maximum point of `u ↦ r(x,u) + Σ_y q_{xy}(u) V_∞(y)`.
`V_∞` is the chain's value through its embedded model (`Vinf`, Theorem 8.2.1). -/
theorem theorem_8_3_1 (Ch : MDChain E U) (b : E → ℝ) (cr cQ : ℝ)
    (hbound : IsUpperBoundingFunctionChain Ch b cr cQ) (hαb : cQ * (Ch.lam / (Ch.β + Ch.lam)) < 1)
    (hUcompact : IsCompact (Set.univ : Set U))
    (hqcont : ∀ x y, Continuous (Ch.q x y))
    (hbsum_cont : ∀ x, Continuous fun u => (∑' y, ENNReal.ofReal (Ch.Qy x y u * b y)).toReal)
    (hrusc : ∀ x, UpperSemicontinuous fun u => Ch.r (x, u)) :
    (Ch.Vinf ∈ IBbPlus b ∧
        ∀ x, (Ch.β : EReal) * Ch.Vinf x = ⨆ u : U, (((Ch.r (x, u) : ℝ) : EReal) +
          (Ch.lam : EReal) * (erealIntegral (Ch.Qmeas x u) Ch.Vinf - Ch.Vinf x))) ∧
      ∃ fstar : E → U, Measurable fstar ∧
        (∀ x, ((Ch.r (x, fstar x) : ℝ) : EReal) +
            (Ch.lam : EReal) * (erealIntegral (Ch.Qmeas x (fstar x)) Ch.Vinf - Ch.Vinf x) =
          ⨆ u : U, (((Ch.r (x, u) : ℝ) : EReal) +
            (Ch.lam : EReal) * (erealIntegral (Ch.Qmeas x u) Ch.Vinf - Ch.Vinf x))) ∧
        ∀ x, Ch.Jinf (fun _ => fstar) x = Ch.Vinf x := by sorry

end MDPFinance.PDMDP
