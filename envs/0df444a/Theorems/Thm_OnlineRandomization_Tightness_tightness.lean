-- Prove2me | Theorems.Thm_OnlineRandomization_Tightness_tightness
-- name    : OnlineRandomization.Tightness.tightness
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T07:15:21.075251+00:00
-- url     : https://prove2.me/theorems/ff6b628e-568c-4108-9ac1-2376b70a763a
-- title:
--   §2, p. 11 — the bound $\alpha\beta$ of Theorem 2.2 against adaptive off-line adversaries is tight
-- statement:
--   Theorem 2.2 shows that a randomized algorithm that is $\alpha$-competitive against adaptive on-line adversaries and $\beta$-competitive against oblivious adversaries is $\alpha\beta$-competitive against adaptive off-line adversaries. This statement says the bound $\alpha\beta$ cannot be lowered in general.
--
--   Let $\alpha, \beta$ be reals with $1 < \beta \le \alpha$, or $\alpha = \beta = 1$, and let $C < \alpha\beta$. Then there exist a request-answer game (a request set $R$, a finite nonempty answer set $A$ and real cost functions $f_n$) and a randomized on-line algorithm $G$ such that
--
--   1. $G$ is $\alpha$-competitive against any adaptive on-line adversary;
--   2. $G$ is $\beta$-competitive against any oblivious adversary;
--   3. for every randomized on-line algorithm $K$ there is an adaptive off-line adversary $Q$ against which $K$'s competitive ratio is at least $C$:
--   $$
--   \mathbb E\bigl[c_Q(K)\bigr] > 0 \qquad\text{and}\qquad \mathbb E\bigl[c_K(Q)\bigr] \ge C \cdot \mathbb E\bigl[c_Q(K)\bigr].
--   $$
--
--   Here competitiveness is with the ratio functions $x \mapsto \alpha x$ and $x \mapsto \beta x$, $c_K(Q)$ is the algorithm's cost against $Q$, and $c_Q(K)$ is the adversary's cost, the off-line optimum of the requests it made.
--
--   **Formalization Note.** The page states the range $1 \le \beta \le \alpha$. Its construction fails at $\beta = 1 < \alpha$ (the solution has $m < 1$ for every $t$, and $G$ is then not $1$-competitive against oblivious adversaries), so this statement covers $1 < \beta \le \alpha$ and the trivial case $\alpha = \beta = 1$; the case $\beta = 1 < \alpha$ is left out. In fact the claim is false there for $1 < C < \alpha$: an algorithm that is $1$-competitive against oblivious adversaries answers optimally, almost surely, on every request sequence (its cost is never below the optimum and its expected cost does not exceed it), and an adaptive off-line adversary reaches only finitely many request sequences, so against $K = G$ every adversary has $\mathbb E[c_G(Q)] = \mathbb E[c_Q(G)]$, a ratio of $1 < C$. The positivity $\mathbb E[c_Q(K)] > 0$ excludes the adversary that asks nothing, for which $0 \ge C \cdot 0$ would hold vacuously. The game's types are existentially quantified in `Type`; "every algorithm $K$" ranges over randomized algorithms whose coin space is a type in `Type`, with deterministic algorithms as the one-point case. Costs are real numbers (the paper allows $\infty$). Expectations are Bochner integrals over the coins.
-- source:
--   Ben-David, Borodin, Karp, Tardos and Wigderson, On the power of randomization in on-line algorithms, Algorithmica 11 (1994), manuscript p. 11, §2, tightness of Theorem 2.2 (construction pp. 12-13)

import Mathlib
import Definitions.Def_OnlineRandomization_Tightness_Model

namespace OnlineRandomization.Tightness

open MeasureTheory

/-- Manuscript p. 11, §2, tightness of Theorem 2.2 (construction pp. 12–13), for
`1 < β ≤ α` (and the trivial case `α = β = 1`): for every `C < αβ` there are a request-answer
game and a randomized algorithm `G` that is `α`-competitive against any adaptive on-line
adversary and `β`-competitive against any oblivious adversary, while against every randomized
algorithm `K` some adaptive off-line adversary forces the ratio `C` (with a positive expected
adversary cost). -/
theorem tightness (α β C : ℝ) (hαβ : (1 < β ∧ β ≤ α) ∨ (β = 1 ∧ α = 1)) (hC : C < α * β) :
    ∃ (R A Ω : Type) (_ : Fintype A) (_ : Nonempty A) (_ : MeasurableSpace Ω)
      (F : Game R A) (G : RandAlg R A Ω),
      IsCompetitiveOnline F (fun x => α * x) G ∧
      IsCompetitiveObl F (fun x => β * x) G ∧
      ∀ (Ω' : Type) [MeasurableSpace Ω'] (K : RandAlg R A Ω'),
        ∃ Q : OfflineAdv R A,
          0 < ∫ ω, advCostOffline F (K.alg ω) Q ∂K.μ ∧
          C * ∫ ω, advCostOffline F (K.alg ω) Q ∂K.μ ≤
            ∫ ω, algCostOffline F (K.alg ω) Q ∂K.μ := by sorry

end OnlineRandomization.Tightness
