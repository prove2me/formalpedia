-- Prove2me | Theorems.Thm_GSRandomOrder_theorem_3_1
-- name    : GSRandomOrder.theorem_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T17:03:58.977997+00:00
-- url     : https://prove2.me/theorems/d90e4891-412a-4e9f-947e-44901ba25ab0
-- title:
--   Theorem 3.1 — selection: every item of $D_v(N)$ is accepted with probability exactly $1/e$, and $\mathbb E\,v(A)\ge\mathrm{OPT}(v)/e$
-- statement:
--   Let $v:2^N\to\mathbb R\cup\{-\infty\}$ be a GS valuation, and run the survival algorithm with independent arrival times uniform on $[0,1]$. The acceptance probability (9) always lies in $[0,1]$, and the accepted set $A$ satisfies:
--
--   1. $P[g\in A]=1/e$ for every $g\in D_v(N)$;
--   2. at every time, $A\subseteq D_v(T)$ for some set $T$ of arrived items, so $A$ is feasible ($v(A)>-\infty$) and $v(A)\ge0$;
--   3. $$\mathbb E\,v(A)\ge\frac{\mathrm{OPT}(v)}{e}.$$
--
--   Parts 1 and 3 are Theorem A of the paper: an online algorithm with value queries on arrived sets achieves $1/e$ of the optimum for every signed GS valuation, possibly taking the value $-\infty$, which is best possible. Part 2 is what the welfare result builds on.
--
--   **Formalization Note** The randomness is the arrival times and one uniform acceptance coin per item; step 3 accepts iff the coin is below $\alpha_x$. The first clause is asserted at every state $(S,x,t,A)$ with $x\notin S$, $x\in D_v(S+x)$, $t\in[1/e,1]$, $A\subseteq S$. Part 2 is asserted on every sample path and at every real time, with $v\ge0$ on every subset of $A$. In part 3, $v(A)$ is read as a real number, which is exact by part 2.
--
--   Differences from the source:
--   - encoding: GS valuation (Definition 2.1, equivalently the exchange axiom (3) by the cited Theorem 2.3, p.6), values in ℝ ∪ {−∞} → IsGSValuation v: v ∅ = 0 and the exchange axiom (3), v : Finset (Fin n) → WithBot ℝ; reason: the paper defines a GS valuation as one with the two equivalent properties and all its proofs use (3); ⊥ = −∞
--   - encoding: items arrive in uniformly random order; the algorithm accepts with probability α_x → continuous-time model of §3.1: i.i.d. Unif[0,1] arrival times and one uniform coin per item (accept iff coin < α_x), ties broken by label; reason: the paper states and proves Theorem 3.1 in this model and reduces random order to it (p.9); ties have probability zero
--   - generalization: the acceptance probability (9) always lies in [0, 1] (at the states the algorithm reaches) → 0 ≤ α_x(A, S, t) ≤ 1 for every S, x ∉ S with x ∈ D_v(S + x), t ∈ [1/e, 1] and A ⊆ S; reason: every state the algorithm reaches in step 3 is of this form, with t > 1/e
--   - generalization: v(A) ≥ 0 → 0 ≤ v(Y) for every Y ⊆ A; reason: Y = A gives the printed clause
--   - encoding: E v(A) and OPT(v) → ∫ (v A).unbotD 0 and opt v = (sup over all S of v S).unbotD 0; reason: v(A) is finite on every sample path by part (ii), and OPT(v) ≥ v(∅) = 0
-- source:
--   Paes Leme, Pál, Patel, Gross Substitutes Welfare in Random Order, STOC 2027 submission (manuscript sha256 69787f50…), Theorem 3.1, p.10 (contains Theorem A, p.4)

import Mathlib
import Definitions.Def_GSRandomOrder_IsGSValuation
import Definitions.Def_GSRandomOrder_canonicalDemand
import Definitions.Def_GSRandomOrder_acceptProb
import Definitions.Def_GSRandomOrder_runSurvival
import Definitions.Def_GSRandomOrder_opt

set_option autoImplicit false

open MeasureTheory

namespace GSRandomOrder

/-- **Theorem 3.1 (Selection)** (R. Paes Leme, M. Pál, N. Patel, *Gross Substitutes Welfare in
Random Order*, STOC 2027 submission, manuscript sha256 69787f50…, §3.2, p.10; it contains
Theorem A, p.4, as parts (i) and (iii)). Let `v : 2^N → ℝ ∪ {−∞}` be a GS valuation. In the
survival algorithm the acceptance probability (9) always lies in `[0, 1]`, and the accepted set
`A` satisfies:
(i) `P[g ∈ A] = 1/e` for every `g ∈ D_v(N)`;
(ii) at every time, `A ⊆ D_v(T)` for some set `T` of arrived items, so `A` is feasible and
`v(A) ≥ 0`;
(iii) `E v(A) ≥ OPT(v)/e`.

**Formalization Note.**
* The algorithm is `runSurvival` in the continuous-time model of §3.1: independent arrival times
  `t_g` uniform on `[0, 1]` and one independent uniform acceptance coin per item (the sample space
  `Ω n` with `volume`); item `x` is accepted in step 3 iff its coin is below `α_x`. The
  random-order model reduces to this one (p.9).
* The first clause is stated at every admissible state: every `S`, every `x ∉ S` with
  `x ∈ D_v(S + x)`, every `t ∈ [1/e, 1]` and every `A ⊆ S` (the states the algorithm reaches have
  `t > 1/e`).
* (ii) is stated on every sample path `ω` and at every real time `s` (the printed clause carries
  no "almost surely"), with `T` a subset of the items arrived by time `s`; "feasible" is `v(A) ≠ −∞`, and `v ≥ 0` is stated on every subset of `A`
  (which contains the printed `v(A) ≥ 0`).
* (iii) reads `v(A)` as a real number with `unbotD 0`, which is exact because of (ii); `OPT(v)` is
  `opt v` and `1/e = Real.exp (-1)`. -/
theorem theorem_3_1 {n : ℕ} (v : Finset (Fin n) → WithBot ℝ) (hv : IsGSValuation v) :
    (∀ (S : Finset (Fin n)) (x : Fin n) (t : ℝ) (A : Finset (Fin n)), x ∉ S →
      x ∈ canonicalDemand v (insert x S) → t ∈ Set.Icc (Real.exp (-1)) 1 → A ⊆ S →
        0 ≤ acceptProb v x A S t ∧ acceptProb v x A S t ≤ 1) ∧
    (∀ g ∈ canonicalDemand v Finset.univ,
      volume {ω : Ω n | g ∈ finalAccepted v ω} = ENNReal.ofReal (Real.exp (-1))) ∧
    (∀ ω : Ω n, ∀ s : ℝ, ∃ T ⊆ arrivedBy ω s,
      acceptedBy v ω s ⊆ canonicalDemand v T ∧ v (acceptedBy v ω s) ≠ ⊥ ∧
        ∀ Y ⊆ acceptedBy v ω s, 0 ≤ v Y) ∧
    opt v / Real.exp 1 ≤ ∫ ω : Ω n, (v (finalAccepted v ω)).unbotD 0 := by sorry

end GSRandomOrder
