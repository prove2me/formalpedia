-- Prove2me | Theorems.Thm_NashOrTriangle_Supplement_theorem_3_1
-- name    : NashOrTriangle.Supplement.theorem_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T04:48:43.8502+00:00
-- url     : https://prove2.me/theorems/5686f48d-63c7-45f3-aef3-d0e06d9a01b5
-- title:
--   Theorem 3.1 — deterministic algorithms for $\mathrm{NorT}(k,t)$ need $2^{c_1t}$ BR calls
-- statement:
--   **Theorem 3.1.** There are universal constants $c_1,C>0$ with the following property. Let $k\ge 8$ and $t\ge C$ be integers. For every deterministic algorithm in the oracle model there is a finite binary game with no $t$-triangle, together with an exact best-response oracle for it, on which the algorithm does not halt with a correct answer to $\mathrm{NorT}(k,t)$ after fewer than
--   $$2^{c_1 t}$$
--   BR calls. In other words, every deterministic algorithm that solves $\mathrm{NorT}(k,t)$ with exact BR oracles needs at least $2^{c_1t}$ BR calls in the worst case, even when the game is finite and is promised to have no $t$-triangle.
--
--   A correct answer is a $1/k$-Nash equilibrium $(p,q)$ of finite rational mixtures of known strategies, $U(q)-M(p,q)\le1/k$ and $M(p,q)-L(p)\le1/k$, or a $t$-triangle of known strategies. The defeating oracle is oblivious: a fixed response map, chosen with knowledge of the algorithm.
--
--   The theorem shows that the exponential dependence on $t$ of the upper bound of Theorem 2.1 is necessary for deterministic algorithms; an exact BR oracle is a $\delta$-BR oracle for every $\delta\ge0$, so the bound holds verbatim for approximate oracles.
--
--   **Formalization Note** An algorithm is any program of the published oracle machine on any input memory, so it may depend on $k$ and $t$. Only BR calls are counted.
--
--   Differences from the source:
--   - encoding: every deterministic algorithm in the oracle model → every program of the published oracle machine (real literals allowed) on every input memory; reason: the published model of the base mission; quantifying over every input memory lets the algorithm depend on k and t
--   - reading: needs at least 2^{c1 t} BR calls in the worst case → for every program there are a finite binary game without a t-triangle and an exact oblivious BR oracle on which the run does not halt with fewer than 2^{c1 t} BR calls and a correct answer; reason: worst case over games and oracles; §1.1 says the lower bounds hold against oblivious adversaries who fix the BR oracle knowing the algorithm
--   - encoding: solves NorT(k, t) → halts with IsNorTNashAnswer: a 1/k-Nash pair of finite rational mixtures of known strategies or a t-triangle of known strategies; reason: Definition 1.1, with outputs finitely supported and rational
-- source:
--   Daskalakis–Papadimitriou–Yannakakis, On the Complexity of Infinite Zero-Sum Games, STOC 2027 submission (manuscript sha256 4f8d0962cc2efb135d3833e902fa4e861e03acf9d2df3fe8140a50b646da66f7), Theorem 3.1, p.5 (PDF p.6)

import Mathlib
import Definitions.Def_NashOrTriangle_OracleMachine
import Definitions.Def_NashOrTriangle_HaltsWith
import Definitions.Def_NashOrTriangle_IsBinary
import Definitions.Def_NashOrTriangle_HasTriangle
import Definitions.Def_NashOrTriangle_Supplement_NashAnswer
import Definitions.Def_NashOrTriangle_Supplement_IsOblivious

namespace NashOrTriangle.Supplement

/-- **Theorem 3.1** (an exponential lower bound for deterministic algorithms). There are universal
constants `c₁, C > 0` with the following property. For all integers `k ≥ 8` and `t ≥ C`, every
deterministic algorithm that solves `NorT(k, t)` with exact BR oracles needs at least `2^{c₁ t}` BR
calls in the worst case. This holds even when the game is finite and is promised to have no
`t`-triangle.

Source: Daskalakis–Papadimitriou–Yannakakis, *On the Complexity of Infinite Zero-Sum Games*,
STOC 2027 submission manuscript (sha256 4f8d0962…66f7), Theorem 3.1, printed p. 5 (PDF p. 6).

**Formalization Note** A deterministic algorithm is any program of the published oracle machine
(real literals allowed) on any input memory, so it may depend on `k` and `t` and read them in any
form. "Needs at least `2^{c₁t}` BR calls in the worst case" is stated as: some finite binary game
without a `t`-triangle and some exact BR oracle make the run fail to halt with fewer than
`2^{c₁t}` BR calls and a correct answer. The oracle is oblivious (a fixed response map, chosen
with knowledge of the program, §1.1). A correct answer is a `1/k`-Nash equilibrium of finite
rational mixtures of known strategies or a `t`-triangle (`IsNorTNashAnswer`); utility calls and
local computation are free. -/
theorem theorem_3_1 :
    ∃ c₁ C : ℝ, 0 < c₁ ∧ 0 < C ∧ ∀ k t : ℕ, 8 ≤ k → C ≤ (t : ℝ) →
      ∀ (P : Program) (x : ℤ → ℝ),
        ∃ (A B : Type) (_ : Fintype A) (_ : Fintype B) (_ : Nonempty A) (_ : Nonempty B)
          (M : A → B → ℚ), IsBinary M ∧ ¬ HasTriangle M t ∧
          ∃ adv : BRAdversary M 0, IsOblivious adv ∧
            ¬ HaltsWith P M adv x (fun s =>
              (s.brCalls : ℝ) < (2 : ℝ) ^ (c₁ * (t : ℝ)) ∧ IsNorTNashAnswer M k t s) := by sorry

end NashOrTriangle.Supplement
