-- Prove2me | Theorems.Thm_OnlineRandomization_Restart_theorem_4_1
-- name    : OnlineRandomization.Restart.theorem_4_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T08:37:13.511242+00:00
-- url     : https://prove2.me/theorems/038790eb-249b-4a0e-81c0-329d81731a4b
-- title:
--   Theorem 4.1, p. 17 — restarting an algorithm on $R_H$, $H = (2+\epsilon)D(F)/\epsilon$, is a $(1+\epsilon)\alpha$-competitive deterministic algorithm
-- statement:
--   Let $F$ be a request-answer game with a finite nonempty request set $R$ and a finite nonempty answer set $A$. Assume that
--
--   1. $F$ is monotone and local;
--   2. $f_0 \ge 0$ (the empty play has nonnegative cost);
--   3. $D$ is a bound on the diameter of $F$ (so $F$ has finite diameter $D(F) \le D$).
--
--   Let $\alpha(x) = d\,x$ with $d \ge 1$, let $\epsilon > 0$, and put
--
--   $$H = \frac{(2+\epsilon) D}{\epsilon}.$$
--
--   Then:
--
--   1. the set $R_H$ is finite;
--   2. the restart algorithm built from any $A_H$ depends only on the values of $A_H$ on $R_H$;
--   3. for every deterministic online algorithm $A_H$ that is $\alpha$-competitive on $R_H$, i.e. $c_{A_H}(r) \le d\, c(r)$ for all $r \in R_H$, the restart algorithm built from $A_H$ is $(1+\epsilon)\alpha$-competitive:
--   $$c_{\mathrm{Restart}}(r) \le (1+\epsilon)\, d\, c(r) \quad \text{for every request sequence } r.$$
--
--   This is the constructive content of Theorem 4.1. Theorem 2.1 of the paper shows that an $\alpha$-competitive randomized algorithm against adaptive off-line adversaries yields a deterministic $\alpha$-competitive algorithm, but not how to compute it. Theorem 4.1 replaces it by a finite object: an algorithm $A_H$ that only has to be good on the finite set $R_H$, extended to all request sequences by restarting, at the price of a factor $1+\epsilon$.
--
--   **Formalization Note** The paper's hypothesis "there exists a randomized online algorithm that is $\alpha$-competitive against every offline adaptive adversary" serves only to produce, via Theorem 2.1, an algorithm $A_H$ that is $\alpha$-competitive on $R_H$; the statement here quantifies over every such $A_H$ instead, so it does not need that hypothesis. "Computable" has no precise meaning for real-valued costs (the paper says so of Corollary 3.1); its content is represented by parts 1 and 2: the restart algorithm is determined by a finite table. For a deterministic algorithm, competitiveness against every adaptive off-line adversary is competitiveness on every request sequence, which is how part 3 is stated. Pins: costs are real (the paper allows $+\infty$); finite diameter is a real bound $D$ and the theorem holds for each, in particular $D = D(F)$; $f_0 \ge 0$ is added (it makes all costs nonnegative, which the proof uses for the last segment, and holds in the paper's examples); $\alpha(x) = d\,x$ with $d \ge 1$ rather than a general linear function, since with $H = (2+\epsilon)D/\epsilon$ the final inequality needs $(2+\epsilon) d \ge 1 + (1+\epsilon) d$; $(1+\epsilon)\alpha$ is $x \mapsto (1+\epsilon) d x$; $R$ is nonempty.
-- source:
--   Ben-David, Borodin, Karp, Tardos and Wigderson, On the power of randomization in on-line algorithms, Algorithmica 11 (1994), manuscript p. 17, Theorem 4.1, with the construction of its proof, p. 18

import Mathlib
import Definitions.Def_OnlineRandomization_Restart_Model
import Definitions.Def_OnlineRandomization_Restart_GameProperties
import Definitions.Def_OnlineRandomization_Restart_RestartAlgorithm

namespace OnlineRandomization.Restart

/-- Theorem 4.1 (p. 17), through its construction (p. 18). Let `F` be a monotone, local game
with finite request set `R`, finite answer set `A`, `f_0 ≥ 0`, and diameter at most `D`.
Let `α(x) = d·x` with `d ≥ 1`, let `ε > 0` and `H = (2 + ε) D / ε`. Then
1. `R_H` is finite;
2. the restart algorithm consults `A_H` only on `R_H`;
3. for every `A_H` that is `α`-competitive on `R_H`, the restart algorithm built from `A_H`
   is `(1 + ε)α`-competitive. -/
theorem theorem_4_1 {R A : Type*} [Fintype R] [Nonempty R] [Fintype A] [Nonempty A]
    (F : Game R A) (hmono : IsMonotone F) (hloc : IsLocal F) (hf0 : 0 ≤ F.cost [] [])
    (D : ℝ) (hD : DiameterBound F D) (d : ℝ) (hd : 1 ≤ d) (ε : ℝ) (hε : 0 < ε) :
    {r : List R | InRH F ((2 + ε) * D / ε) r}.Finite ∧
    (∀ AH AH' : DetAlg R A, (∀ r : List R, InRH F ((2 + ε) * D / ε) r → AH r = AH' r) →
      restart F ((2 + ε) * D / ε) AH = restart F ((2 + ε) * D / ε) AH') ∧
    (∀ AH : DetAlg R A,
      (∀ r : List R, InRH F ((2 + ε) * D / ε) r → AH.costOn F r ≤ d * F.opt r) →
      IsCompetitive F (fun x => (1 + ε) * (d * x)) (restart F ((2 + ε) * D / ε) AH)) := by sorry

end OnlineRandomization.Restart
