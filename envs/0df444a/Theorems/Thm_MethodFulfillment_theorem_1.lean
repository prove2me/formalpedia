-- Prove2me | Theorems.Thm_MethodFulfillment_theorem_1
-- name    : MethodFulfillment.theorem_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:15:26.171189+00:00
-- url     : https://prove2.me/theorems/7ba187f9-3049-4aca-ab5b-37e099ff7dfa
-- title:
--   Theorem 1 — Algorithm 1 with Algorithm 2 is a fulfillment strategy with ratio $\le 1+(\kappa-1)|q_{\max}|/\sqrt{s+3}$
-- statement:
--   Consider any valid online multi-item fulfillment problem. Let $L$ bound the number of items of every order type that can arrive, and let $s\le S_{ik}$ for every pair with $S_{ik}>0$. Then:
--
--   1. the expected LP (6) has an optimal solution;
--   2. for every optimal solution $y$, an Algorithm 2 rule with the inputs (12) exists, and for every such rule, Algorithm 1 run with $y$ and with Algorithm 2 in step 2 of the online process
--      - is a fulfillment strategy: on every run of positive probability, no pair $(i,k)$ ever uses more than its inventory $S_{ik}$; and
--      - has competitive ratio at most
--   $$1+\frac{(\kappa-1)\,L}{\sqrt{s+3}} ,\qquad\text{i.e.}\qquad \mathbb E[\mathrm{ALG}(D)]\le\Big(1+\frac{(\kappa-1)L}{\sqrt{s+3}}\Big)\mathbb E[\mathrm{OPT}(D)] .$$
--
--   With $L=|q_{\max}|$, the size of the largest possible order, and $s$ the smallest positive inventory, this is the bound (13). The guarantee does not depend on the numbers of items, facilities or order types, and it tends to $1$ as the inventories grow.
--
--   **Formalization Note** The ratio is multiplied out. The first bullet of item 2 is the "fulfillment strategy" part of the theorem: Algorithm 2 never checks the remaining stock. The statement covers every optimal LP solution and every joint law of the magicians' coins with the marginals of Algorithm 2.
--
--   Differences from the source:
--   - reading: s = min_{i∈I,k∈K} {Sik} (p.18) → any s ≤ every positive S_ik; reason: Proposition 1 (p.16) and §2 (p.8) define s as the smallest positive S_ik, and the proof of Theorem 1 uses Proposition 1's s; the literal minimum is such an s
--   - generalization: |q_max|, the size of the largest possible order → any L with |q| ≤ L for every q with p_a(q) > 0; reason: |q_max| is such an L; a smaller L gives a stronger bound
--   - reading: "we obtain a fulfillment strategy" → explicit clause: on every run of positive probability usage ≤ S_ik at every t ≤ T; reason: a policy that may ship stock it does not have is not a fulfillment strategy; p.17 and p.59 state it
--   - reading: Algorithm 1 solves the expected LP and obtains y → for every optimal solution y, plus existence of one; reason: the algorithm may use any optimum; quantifying over all is the stronger reading
--   - generalization: Algorithm 2's magicians, each deciding with its own probability → every joint law of the magicians' decisions with these marginals (IsAlg2Rule); reason: the paper does not fix the joint law and its argument does not use one; independent coins are one such law
--   - generalization: Definition 4: the magician starts with S_ik > 0 units (with S_ik < T) → S_ik < T not assumed; reason: the recursion needs no such condition; the case S_ik < T is included
--   - encoding: competitive ratio E[ALG(D)]/E[OPT(D)] at most B → E[ALG(D)] ≤ B · E[OPT(D)]; reason: cross-multiplied; equivalent when E[OPT(D)] > 0 and not vacuous at 0/0
--   - encoding: the online process with history-dependent, possibly randomized decision rules → an explicit law runProb on runs (arrival, drawn method, available set) with non-anticipating kernels; reason: same law; the run records every decision
--   - encoding: a dummy facility 0 with infinite inventory; the discard method m′(q) uses it for all items of q → a method is its set of real-facility pairs; the discard method is ∅; methods and costs are indexed by their order type; reason: Lean convention; the same instances
--   - encoding: periods t ∈ [T] = {1,…,T}; arrivals D_qt → 0-based Fin T (Lean t is the paper's t + 1); arrivals as Option Q, none = no arrival; reason: Lean convention; the same instances
--   - encoding: c_{m′(q)}/c_m ≤ κ → c q ∅ ≤ κ * c q m, with no positivity assumption on costs; reason: cross-multiplied; with c q m ≤ c q ∅ and κ > 1 it forces c ≥ 0, so it excludes only undefined cases
--   - generalization: not fulfilling costs more than any other method (p.7, "higher") → c q m ≤ c q ∅ (ties allowed); reason: p.36 assumes the discard method is the "largest"; allowing equality covers the strict case
--   - encoding: inventories Sik ≥ 0 → S_ik ∈ ℕ; reason: inventory is counted in units (p.15, "one unit")
-- source:
--   Amil, Makhdoumi & Wei, Multi-Item Order Fulfillment Revisited: LP Formulation and Prophet Inequality, manuscript (PDF sha256 197c13b9…), Theorem 1, pp.17–18, (13); proof p.18

import Mathlib
import Definitions.Def_MethodFulfillment_Instance
import Definitions.Def_MethodFulfillment_Valid
import Definitions.Def_MethodFulfillment_pa
import Definitions.Def_MethodFulfillment_expOPT
import Definitions.Def_MethodFulfillment_IsLPOpt
import Definitions.Def_MethodFulfillment_runProb
import Definitions.Def_MethodFulfillment_usage
import Definitions.Def_MethodFulfillment_mu
import Definitions.Def_MethodFulfillment_expALG
import Definitions.Def_MethodFulfillment_IsAlg2Rule

namespace MethodFulfillment

/-- **Theorem 1** (Amil, Makhdoumi & Wei, manuscript, PDF sha256 197c13b9…, Theorem 1, pp.17–18,
(13)): when Algorithm 1 uses Algorithm 2 in step 2 of the online process, it is a fulfillment
strategy with competitive ratio at most `1 + (κ − 1)|q_max|/√(s + 3)`. Precisely, for every valid
instance, every bound `L` on the size of the order types that can arrive and every `s` at most
every positive inventory:
1. the expected LP (6) has an optimal solution;
2. for every optimal solution `y` an Algorithm 2 rule exists, and for every Algorithm 2 rule `ρ`:
   (a) on every run of positive probability no pair ever uses more than its inventory, and
   (b) `E[ALG(D)] ≤ (1 + (κ − 1) L/√(s + 3)) · E[OPT(D)]`.

**Formalization Note.** The ratio is cross-multiplied. Clause (a) is the "fulfillment strategy"
part of the statement: Algorithm 2 never checks the stock. -/
theorem theorem_1 {I K Q : Type} [Fintype I] [DecidableEq I] [Fintype K] [DecidableEq K]
    [Fintype Q] [DecidableEq Q] {T : ℕ} (P : Instance I K Q T) (hP : Valid P)
    (L : ℕ) (hL : ∀ q, 0 < pa P q → (P.items q).card ≤ L)
    (s : ℕ) (hs : ∀ (i : I) (k : K), 0 < P.S i k → s ≤ P.S i k) :
    (∃ y, IsLPOpt P y) ∧
      ∀ y, IsLPOpt P y →
        (∃ ρ, IsAlg2Rule P (mu' P y) ρ) ∧
          ∀ ρ, IsAlg2Rule P (mu' P y) ρ →
            (∀ r, 0 < runProb P y (alg2Policy ρ) r → ∀ t ≤ T, ∀ (i : I) (k : K),
                usage r t i k ≤ P.S i k) ∧
              expALG P y (alg2Policy ρ) ≤
                (1 + (P.κ - 1) * (L : ℝ) / Real.sqrt ((s : ℝ) + 3)) * expOPT P := by sorry

end MethodFulfillment
