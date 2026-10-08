-- Prove2me | Theorems.Thm_NegativeDP_Stationary_theorem51g
-- name    : NegativeDP.Stationary.theorem51g
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:54:41.425391+00:00
-- url     : https://prove2.me/theorems/0c97f39d-a645-4331-bf0d-d4f79dc30ec8
-- title:
--   Theorem 5.1 (g) (N) — for a Markov policy, Iₙ(π, v) = T₁ ⋯ Tₙ v
-- statement:
--   In the negative dynamic programming problem, let $\pi=\{f_1,f_2,\dots\}$ be a (non-random) Markov policy and $T_k$ the operator of $f_k$. Then for every $n$ and every $v\in M(S)$,
--
--   $$I_n(\pi,v)=T_1T_2\cdots T_n\,v ,$$
--
--   where $I_n(\pi,v)$ is the expected return of the first $n$ stages plus the terminal reward $v(s_{n+1})$. For $n=0$ both sides are $v$. The paper states Theorem 5.1 for the discounted, positive and negative cases; this item is the negative case.
--
--   **Formalization Note.** Lean numbers the rules $m_0,m_1,\dots$ (the paper's $f_1,f_2,\dots$), and $T_1\cdots T_nv$ is the right fold $T_{m_0}(T_{m_1}(\cdots T_{m_{n-1}}v))$.
-- source:
--   Strauch, Negative Dynamic Programming, Ann. Math. Statist. 37 (1966), p. 879, Theorem 5.1 (g)

import Mathlib
import Definitions.Def_DiscountedDP_Stationary_Model
import Definitions.Def_DiscountedDP_Stationary_Return
import Definitions.Def_NegativeDP_Stationary_Model
open MeasureTheory ProbabilityTheory Filter Topology
open DiscountedDP.Stationary (Hist Plan MarkovPlan MarkovPlan.toPlan stationary)

namespace NegativeDP.Stationary

variable {S A : Type*} [MeasurableSpace S] [StandardBorelSpace S] [Nonempty S]
  [MeasurableSpace A] [StandardBorelSpace A] [Nonempty A]

/-- Theorem 5.1 (g), case N (p. 879): for a Markov policy `π = {f₁, f₂, …}` with operators
`Tₖ` of `fₖ`, `Iₙ(π, v) = T₁ ⋯ Tₙ v` for every `v ∈ M(S)`. In Lean the rules are
`m 0, m 1, …` and `T₁ ⋯ Tₙ v` is the right fold over `0, …, n - 1`. -/
theorem theorem51g (P : Problem S A) (m : MarkovPlan S A) (n : ℕ) (v : S → EReal)
    (hv : IsNegM v) :
    In P (MarkovPlan.toPlan m) n v = (List.range n).foldr (fun k w => T P (m k) w) v := by sorry

end NegativeDP.Stationary
