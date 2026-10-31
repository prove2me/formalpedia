-- Prove2me | Theorems.Thm_GeomRescale_theorem_3_6
-- name    : GeomRescale.theorem_3_6
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:21:54.4876+00:00
-- url     : https://prove2.me/theorems/0239aa6e-3c89-4ef5-b755-d7a104feff4d
-- title:
--   Theorem 3.6 (corrected: $\log(nL_{f,2})$ replaced by $\ell$): Rescaling-SFM solves SFM
-- statement:
--   There is an absolute constant $C$ with the following property. Let $n \ge 1$, let $f : 2^V \to \mathbb{Z}$ be submodular with $f(\emptyset) = 0$ on an $n$-element set $V$, let $\Lambda \ge L_{f,2}$, $T = \lceil 5n \log_2(n\Lambda) \rceil_+$, and $\ell = 1 + \max\{0, \log_2(n\Lambda)\}$. For Algorithm Rescaling-SFM with every tie-break, every argmin and every arbitrary vertex:
--
--   1. every reachable state that is not final has a successor;
--   2. every run has at most $3 + T(400n^2 + 3)$ states;
--   3. every returned set $W$ satisfies $f(W) \le f(S)$ for all $S \subseteq V$;
--   4. every terminating run satisfies, for every $\mathrm{EO} \ge 0$,
--
--   $$\mathrm{evals} \cdot \mathrm{EO} + \mathrm{ops} \le C(n^4 \cdot \mathrm{EO} + n^5)\, \ell.$$
--
--   With $\Lambda = L_{f,2}$ this is the printed theorem: Algorithm Rescaling-SFM finds an optimal solution to (SFM) in time $O((n^4 \cdot \mathrm{EO} + n^5)\log(nL_{f,2}))$, wherever $nL_{f,2} \ge 2$, since $\ell \le 2\log_2(nL_{f,2})$ there. With $\Lambda = \|\alpha\|_2$ it is the note under the theorem.
--
--   Differences from the source:
--   - correction: time $O((n^4 \cdot \mathrm{EO} + n^5)\log(nL_{f,2}))$ → the factor $\ell = 1 + \max\{0, \log_2(n\Lambda)\}$; reason: at $n = 1$, $f(\{v\}) = 1$ the printed bound is $0$ while $f(V)$ is evaluated, and for $f \equiv 0$ it is undefined; $\ell \le 2\log_2(n\Lambda)$ for $n\Lambda \ge 2$
--   - generalization: $T$ computed from $L_{f,2}$ → $T$ computed from any $\Lambda \ge L_{f,2}$; reason: $\Lambda = L_{f,2}$ is the printed theorem, and $\Lambda = \|\alpha\|_2$ the note under it
--   - reading: $T = 5n\log(nL_{f,2})$ → $T = \lceil 5n \log_2(n\Lambda) \rceil_+$; reason: $T$ must be a natural number and the proof's display needs base $2$
--   - reading: time, counted by line in the proof → the counters `evals`, `ops` with the charge table, for all $\mathrm{EO} \ge 0$; reason: the paper gives no machine; $f$ is read only in charged steps
--   - reading: $g/\|g\|_Q$ with no case for $g = 0$ → $g/\|g\|_Q := 0$ at $g = 0$; reason: $g = 0$ occurs for $f \equiv 0$; the algorithm then stops at line 6
--   - encoding: the algorithm finds an optimal solution → progress, bounded runs, correctness of every returned set; reason: a relation over all choices rules out both a stuck model and a fuel cut-off
--   - encoding: a ground set $V$ with $n = |V|$ elements → `1 ≤ n`; reason: the parameter $\varepsilon = 1/(20n)$ of Algorithm 2 is undefined at $n = 0$; the hypothesis excludes only that case
--   - reading: $g_1, \dots, g_k$ in (10) and in line 8 of Algorithm 2, returned after line 15 of Algorithm 1 incremented $k$ → $g_1, \dots, g_{k-1}$, the bases the call computed; reason: line 15 has incremented $k$, so no $g_k$ was computed
-- source:
--   Dadush, Végh & Zambelli, Geometric Rescaling Algorithms for Submodular Function Minimization, arXiv:1707.05065v4, Theorem 3.6, p.10

import Mathlib
import Definitions.Def_NonmonotoneSubmod_Shared_Submodular
import Definitions.Def_GeomRescale_fR
import Definitions.Def_GeomRescale_ell
import Definitions.Def_GeomRescale_numRounds
import Definitions.Def_GeomRescale_Ltwo
import Definitions.Def_GeomRescale_Reachable
import Definitions.Def_GeomRescale_IsRun

open NonmonotoneSubmod.Shared
open SchrijverSFM.Alg

namespace GeomRescale

/-- Theorem 3.6 (Dadush, Végh & Zambelli, Geometric Rescaling Algorithms for Submodular Function Minimization, arXiv:1707.05065v4, Theorem 3.6, p.10): Algorithm Rescaling-SFM finds an optimal solution to
(SFM) in time `O((n⁴ · EO + n⁵) log(nL_{f,2}))`.

There is an absolute constant `C` such that for every `n ≥ 1`, every integer valued submodular `f`
with `f(∅) = 0` and every `Λ ≥ L_{f,2}`, with `ℓ = 1 + max {0, log₂(nΛ)}`:

1. every reachable state that is not final has a successor;
2. every run has at most `3 + T (400n² + 3)` states;
3. every reachable final state `done W` has `f(W) ≤ f(S)` for all `S ⊆ V`;
4. every reachable final state has `evals · EO + ops ≤ C (n⁴ · EO + n⁵) ℓ` for every `EO ≥ 0`.

**Formalization Note.** `Λ` is a parameter of the run used only in `T`: `Λ = L_{f,2}` is the theorem
as printed and `Λ = ‖α‖₂` is the note under it. The factor is `ℓ` rather than `log(nL_{f,2})`, since
the printed factor vanishes at `n = 1`, `f({v}) = 1`, and is undefined for `f ≡ 0`, while `f(V)` is
evaluated; `ℓ ≤ 2 log₂(nΛ)` for `nΛ ≥ 2`. All tie-breaks, argmins and arbitrary vertices are covered,
since the run is a relation. Time is `evals`, `ops` of the charge table: `f` is read only in steps
that pay for it, and clause 4 for all `EO ≥ 0` bounds both counters. -/
theorem theorem_3_6 :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ), 1 ≤ n → ∀ (f : Finset (Fin n) → ℤ), Submodular (fR f) →
      f ∅ = 0 → ∀ Λ : ℝ, Ltwo (fR f) ≤ Λ →
      (∀ s : St n, Reachable f Λ s → (∀ W, s.mode ≠ Mode.done W) → ∃ s', Step f Λ s s') ∧
      (∀ l : List (St n), IsRun f Λ l → l.length ≤ 3 + numRounds n Λ * (400 * n ^ 2 + 3)) ∧
      (∀ (s : St n) (W : Finset (Fin n)), Reachable f Λ s → s.mode = Mode.done W →
        ∀ S, f W ≤ f S) ∧
      (∀ (s : St n) (W : Finset (Fin n)), Reachable f Λ s → s.mode = Mode.done W →
        ∀ EO : ℝ, 0 ≤ EO →
          (s.vn.evals : ℝ) * EO + (s.vn.ops : ℝ) ≤
            C * ((n : ℝ) ^ 4 * EO + (n : ℝ) ^ 5) * ell n Λ) := by sorry

end GeomRescale
