-- Prove2me | Theorems.Thm_MethodFulfillment_proposition_1
-- name    : MethodFulfillment.proposition_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:15:22.804211+00:00
-- url     : https://prove2.me/theorems/0d41a793-ed97-442a-a798-d16715f92c3c
-- title:
--   Proposition 1 — Algorithm 2 is $\left(1-|q_{\max}|/\sqrt{s+3}\right)$-conservative
-- statement:
--   Run Algorithm 1 with a feasible point $y$ of the expected LP and use Algorithm 2, with $\gamma_{ik}=1-1/\sqrt{S_{ik}+3}$ for each pair $(i,k)$ and the consumption probabilities (12) as inputs, in step 2. Let $L$ bound the number of items of every order type that can arrive, and let $s\le S_{ik}$ for every pair with $S_{ik}>0$. Then Algorithm 2 is a $\gamma$-conservative method-acceptance strategy with
--   $$\gamma=1-\frac{L}{\sqrt{s+3}} .$$
--   With $L=|q_{\max}|$, the size of the largest possible order, and $s=\min_{S_{ik}>0}S_{ik}$, this is the paper's $\gamma=1-|q_{\max}|/\sqrt{s+3}$. The magicians' coins may have any joint law with the right marginals.
--
--   **Formalization Note** "For any $m$" is checked in the multiplied-out form of Definition 3, which also covers methods that are never drawn.
--
--   Differences from the source:
--   - generalization: |q_max|, the size of the largest possible order → any L with |q| ≤ L for every q with p_a(q) > 0; reason: |q_max| is such an L; a smaller L gives a stronger bound
--   - generalization: s = min_{Sik>0} Sik → any s with s ≤ S_ik for every S_ik > 0; reason: the minimum is such an s
--   - generalization: y obtained in the offline process (an optimal solution of (6)) → every LP-feasible y; reason: the argument uses only feasibility
--   - generalization: Algorithm 2's magicians, each deciding with its own probability → every joint law of the magicians' decisions with these marginals (IsAlg2Rule); reason: the paper does not fix the joint law and its argument does not use one; independent coins are one such law
--   - generalization: Definition 4: the magician starts with S_ik > 0 units (with S_ik < T) → S_ik < T not assumed; reason: the recursion needs no such condition; the case S_ik < T is included
--   - encoding: P(accepting the method at t | the method is of type m) ≥ γ for any m → Definition 3 multiplied out (IsConservative); reason: equivalent whenever m can be drawn; 0 ≤ 0 otherwise
--   - encoding: the online process with history-dependent, possibly randomized decision rules → an explicit law runProb on runs (arrival, drawn method, available set) with non-anticipating kernels; reason: same law; the run records every decision
--   - encoding: a dummy facility 0 with infinite inventory; the discard method m′(q) uses it for all items of q → a method is its set of real-facility pairs; the discard method is ∅; methods and costs are indexed by their order type; reason: Lean convention; the same instances
--   - encoding: periods t ∈ [T] = {1,…,T}; arrivals D_qt → 0-based Fin T (Lean t is the paper's t + 1); arrivals as Option Q, none = no arrival; reason: Lean convention; the same instances
--   - generalization: not fulfilling costs more than any other method (p.7, "higher") → c q m ≤ c q ∅ (ties allowed); reason: p.36 assumes the discard method is the "largest"; allowing equality covers the strict case
--   - encoding: c_{m′(q)}/c_m ≤ κ → c q ∅ ≤ κ * c q m, with no positivity assumption on costs; reason: cross-multiplied; with c q m ≤ c q ∅ and κ > 1 it forces c ≥ 0, so it excludes only undefined cases
--   - encoding: inventories Sik ≥ 0 → S_ik ∈ ℕ; reason: inventory is counted in units (p.15, "one unit")
-- source:
--   Amil, Makhdoumi & Wei, Multi-Item Order Fulfillment Revisited: LP Formulation and Prophet Inequality, manuscript (PDF sha256 197c13b9…), Proposition 1, p.16; proof pp.16–17

import Mathlib
import Definitions.Def_MethodFulfillment_Instance
import Definitions.Def_MethodFulfillment_Valid
import Definitions.Def_MethodFulfillment_pa
import Definitions.Def_MethodFulfillment_LPFeasible
import Definitions.Def_MethodFulfillment_IsConservative
import Definitions.Def_MethodFulfillment_mu
import Definitions.Def_MethodFulfillment_IsAlg2Rule

namespace MethodFulfillment

/-- **Proposition 1** (Amil, Makhdoumi & Wei, manuscript, PDF sha256 197c13b9…, Proposition 1,
p.16; proof pp.16–17): with `γ_{ik} = 1 − 1/√(S_{ik} + 3)`, Algorithm 2 is a `γ`-conservative
method-acceptance strategy with `γ = 1 − |q_max|/√(s + 3)`.

**Formalization Note.** `|q_max|` is any `L` bounding the number of items of every order type that
can arrive (`pa q > 0`), and `s` is any natural number at most every positive `S_{ik}`; the
paper's `|q_max|` and `s = min_{S_{ik} > 0} S_{ik}` are such values. Every joint law of the
magicians' coins with the right marginals is admitted (`IsAlg2Rule`). -/
theorem proposition_1 {I K Q : Type} [Fintype I] [DecidableEq I] [Fintype K] [DecidableEq K]
    [Fintype Q] [DecidableEq Q] {T : ℕ} (P : Instance I K Q T) (hP : Valid P)
    (y : Q → Finset (I × K) → ℝ) (hy : LPFeasible P y)
    (ρ : Fin T → Run I K Q T → Finset (I × K) → ℝ) (hρ : IsAlg2Rule P (mu' P y) ρ)
    (L : ℕ) (hL : ∀ q, 0 < pa P q → (P.items q).card ≤ L)
    (s : ℕ) (hs : ∀ (i : I) (k : K), 0 < P.S i k → s ≤ P.S i k) :
    IsConservative P y (alg2Policy ρ) (1 - (L : ℝ) / Real.sqrt ((s : ℝ) + 3)) := by sorry

end MethodFulfillment
