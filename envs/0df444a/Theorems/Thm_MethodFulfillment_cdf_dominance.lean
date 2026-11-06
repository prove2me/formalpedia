-- Prove2me | Theorems.Thm_MethodFulfillment_cdf_dominance
-- name    : MethodFulfillment.cdf_dominance
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:15:03.069918+00:00
-- url     : https://prove2.me/theorems/6be420e3-6ff6-4cec-8a11-950be4caca60
-- title:
--   Appendix D, p.58 — the recursion is dominated by the law of $W^t_{ik}$
-- statement:
--   Run Algorithm 1 with a feasible point $y$ of the expected LP and Algorithm 2 in step 2, where the magician of a pair $(i,k)$ with $S_{ik}>0$ is given inputs $\nu^t_{ik}$ that are upper bounds on the consumption probabilities, $\mu^t_{ik}\le\nu^t_{ik}\le1$ (Algorithm 2's own inputs $\nu=\mu$ are included). Let $F^t$ be the recursion of Appendix D with these inputs and $\gamma_{ik}=1-1/\sqrt{S_{ik}+3}$. Then for every period $t$ (up to the end of the horizon) and every $l\ge0$
--   $$F_{W^t_{ik}}(l)\le\Pr\big(W^t_{ik}\le l\big),$$
--   where $W^t_{ik}$ is the number of units of $(i,k)$ consumed before $t$. The magicians' coins may have any joint law with the right marginals.
--
--   This is the step that turns the deterministic recursion into a statement about the actual inventory process.
--
--   **Formalization Note** Lean period $t$ with usage before $t$ is the paper's $W^{t+1}$, and the Lean recursion at $t$ is the paper's $F_{W^{t+1}}$.
--
--   Differences from the source:
--   - generalization: y obtained in the offline process (an optimal solution of (6)) → every LP-feasible y; reason: the argument uses only feasibility
--   - generalization: Algorithm 2's magicians, each deciding with its own probability → every joint law of the magicians' decisions with these marginals (IsAlg2Rule); reason: the paper does not fix the joint law and its argument does not use one; independent coins are one such law
--   - generalization: Definition 4: the magician starts with S_ik > 0 units (with S_ik < T) → S_ik < T not assumed; reason: the recursion needs no such condition; the case S_ik < T is included
--   - encoding: the online process with history-dependent, possibly randomized decision rules → an explicit law runProb on runs (arrival, drawn method, available set) with non-anticipating kernels; reason: same law; the run records every decision
--   - encoding: a dummy facility 0 with infinite inventory; the discard method m′(q) uses it for all items of q → a method is its set of real-facility pairs; the discard method is ∅; methods and costs are indexed by their order type; reason: Lean convention; the same instances
--   - encoding: periods t ∈ [T] = {1,…,T}; arrivals D_qt → 0-based Fin T (Lean t is the paper's t + 1); arrivals as Option Q, none = no arrival; reason: Lean convention; the same instances
--   - generalization: not fulfilling costs more than any other method (p.7, "higher") → c q m ≤ c q ∅ (ties allowed); reason: p.36 assumes the discard method is the "largest"; allowing equality covers the strict case
--   - encoding: c_{m′(q)}/c_m ≤ κ → c q ∅ ≤ κ * c q m, with no positivity assumption on costs; reason: cross-multiplied; with c q m ≤ c q ∅ and κ > 1 it forces c ≥ 0, so it excludes only undefined cases
--   - encoding: inventories Sik ≥ 0 → S_ik ∈ ℕ; reason: inventory is counted in units (p.15, "one unit")
-- source:
--   Amil, Makhdoumi & Wei, Multi-Item Order Fulfillment Revisited: LP Formulation and Prophet Inequality, manuscript (PDF sha256 197c13b9…), Appendix D, p.58

import Mathlib
import Definitions.Def_MethodFulfillment_Instance
import Definitions.Def_MethodFulfillment_Valid
import Definitions.Def_MethodFulfillment_LPFeasible
import Definitions.Def_MethodFulfillment_runProb
import Definitions.Def_MethodFulfillment_usage
import Definitions.Def_MethodFulfillment_mu
import Definitions.Def_MethodFulfillment_gammaS
import Definitions.Def_MethodFulfillment_magF
import Definitions.Def_MethodFulfillment_IsAlg2Rule

namespace MethodFulfillment

/-- **The recursion is dominated by the actual law of the usage** (Amil, Makhdoumi & Wei,
manuscript, PDF sha256 197c13b9…, Appendix D, p.58, "F_{W^t_ik}(l) ≤ P(W^t_ik ≤ l) for all l"):
under Algorithm 1 with Algorithm 2, when the magician of a pair `(i, k)` with `S_{ik} > 0` is given
inputs `ν^t_{ik} ∈ [μ^t_{ik}, 1]` (upper bounds on the consumption probabilities (12), Algorithm 2's
own inputs `ν = μ` included), then for every period `t ≤ T` and every `l`, the recursion `magF`
with `γ_{ik} = 1 − 1/√(S_{ik} + 3)` and the inputs `ν_{ik}` is at most `P(W_{ik} ≤ l)`, the
probability that at most `l` units of `(i, k)` were consumed before `t`.

**Formalization Note.** Lean time `t` with `usage r t` is the paper's `W^{t+1}`, and
`magF … t` is `F_{W^{t+1}}`. -/
theorem cdf_dominance {I K Q : Type} [Fintype I] [DecidableEq I] [Fintype K] [DecidableEq K]
    [Fintype Q] [DecidableEq Q] {T : ℕ} (P : Instance I K Q T) (hP : Valid P)
    (y : Q → Finset (I × K) → ℝ) (hy : LPFeasible P y)
    (ν : I → K → ℕ → ℝ) (ρ : Fin T → Run I K Q T → Finset (I × K) → ℝ) (hρ : IsAlg2Rule P ν ρ)
    (i : I) (k : K) (hν : ∀ t, mu' P y i k t ≤ ν i k t ∧ ν i k t ≤ 1) (hS : 0 < P.S i k)
    (t : ℕ) (ht : t ≤ T) (l : ℕ) :
    magF (ν i k) (gammaS (P.S i k)) t l ≤
      ∑ r, runProb P y (alg2Policy ρ) r * (if usage r t i k ≤ l then 1 else 0) := by sorry

end MethodFulfillment
