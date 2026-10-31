-- Prove2me | Theorems.Thm_GeomRescale_operation_count
-- name    : GeomRescale.operation_count
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:20:48.352773+00:00
-- url     : https://prove2.me/theorems/86a13518-db91-4a48-acea-86f1ee969b2a
-- title:
--   Operation count of a call and of a rescaling
-- statement:
--   There is an absolute constant $C_1$ such that for every $n \ge 1$ and every integer valued submodular $f$ with $f(\emptyset) = 0$:
--
--   1. a call of Algorithm 1 with $\varepsilon = 1/(20n)$, on any valid input, adds at most $C_1 n^3$ to the evaluations of $f$ and at most $C_1 n^4$ to the arithmetic operations, the final test of line 4 included;
--   2. lines 6–8 of Algorithm 2 evaluate $f$ zero times and add at most $C_1 n^4$ operations.
--
--   This is the $O(n^3 \cdot \mathrm{EO} + n^4)$ count per call and the $O(n^4)$ count per rescaling in the paper.
--
--   Differences from the source:
--   - reading: time counted by line in $O$ notation → the counters `evals`, `ops` with the charge table; reason: the paper gives no machine; each charge is at least the cost of the straightforward unit-cost real-arithmetic implementation, up to an absolute factor
--   - generalization: $O(n^3 \cdot \mathrm{EO} + n^4)$, $O(n^4)$ → one absolute constant $C_1$ before $n$ and $f$; reason: this is the $O$ with its quantifiers written out; it also separates the two counters
--   - encoding: a ground set $V$ with $n = |V|$ elements → `1 ≤ n`; reason: the parameter $\varepsilon = 1/(20n)$ of Algorithm 2 is undefined at $n = 0$; the hypothesis excludes only that case
--   - generalization: the run of Algorithm 2 with $T = 5n\log(nL_{f,2})$ → the runs for every $\Lambda \ge L_{f,2}$, with $T = \lceil 5n\log_2(n\Lambda)\rceil_+$; reason: $\Lambda = L_{f,2}$ gives the paper's run, with $T$ rounded as in Theorem 3.6; the statement holds on every such run
--   - reading: $g/\|g\|_Q$ with no case for $g = 0$ → $g/\|g\|_Q := 0$ at $g = 0$ in the step relation; reason: $g = 0$ occurs (for $f \equiv 0$ at line 2 of Algorithm 1), and the run needs a value there
--   - reading: $g_1, \dots, g_k$ in (10) and in line 8 of Algorithm 2, returned after line 15 of Algorithm 1 incremented $k$ → $g_1, \dots, g_{k-1}$, the bases the call computed; reason: line 15 has incremented $k$, so no $g_k$ was computed
-- source:
--   Dadush, Végh & Zambelli, Geometric Rescaling Algorithms for Submodular Function Minimization, arXiv:1707.05065v4, proof of Theorem 3.6, p.12

import Mathlib
import Definitions.Def_NonmonotoneSubmod_Shared_Submodular
import Definitions.Def_GeomRescale_fR
import Definitions.Def_GeomRescale_eps
import Definitions.Def_GeomRescale_Ltwo
import Definitions.Def_GeomRescale_vnStart
import Definitions.Def_GeomRescale_VNStep
import Definitions.Def_GeomRescale_Reachable

open NonmonotoneSubmod.Shared
open SchrijverSFM.Alg

namespace GeomRescale

/-- The operation count of the proof of Theorem 3.6 (Dadush, Végh & Zambelli, Geometric Rescaling Algorithms for Submodular Function Minimization, arXiv:1707.05065v4, proof of Theorem 3.6, p.12), with one
absolute constant `C₁`: a call of Algorithm 1 with `ε = 1/(20n)` increases `evals` by at most `C₁n³`
and `ops` by at most `C₁n⁴`, and lines 6–8 of Algorithm 2 increase `ops` by at most `C₁n⁴` and do not
evaluate `f`.

**Formalization Note.** `C₁` comes before `n`, `f`. The term `n²` in the first clause is the charge of
the final test of line 4, which `Step.exit` adds to `ops`. "Time" is the pair of counters of the charge
table in the docstrings of `vnStart`, `VNStep`, `vnUpdate` and `Step`. -/
theorem operation_count :
    ∃ C₁ : ℝ, 0 < C₁ ∧ ∀ (n : ℕ), 1 ≤ n → ∀ (f : Finset (Fin n) → ℤ), Submodular (fR f) →
      f ∅ = 0 →
      (∀ (μ : ℤ) (W : Finset (Fin n)) (Q : Matrix (Fin n) (Fin n) ℝ) (σ : Equiv.Perm (Fin n))
        (e o : ℕ) (v : VN n), max 0 (-f Finset.univ) ≤ μ → f W = -μ → Q.PosDef →
        Relation.ReflTransGen (VNStep f Q (eps n)) (vnStart f μ W Q σ e o) v →
        (v.evals : ℝ) ≤ e + C₁ * (n : ℝ) ^ 3 ∧
          (v.ops : ℝ) + (n : ℝ) ^ 2 ≤ o + C₁ * (n : ℝ) ^ 4) ∧
      (∀ (Λ : ℝ), Ltwo (fR f) ≤ Λ → ∀ s s' : St n, Reachable f Λ s →
        s.mode = Mode.afterCall → Step f Λ s s' →
        s'.vn.evals = s.vn.evals ∧ (s'.vn.ops : ℝ) ≤ s.vn.ops + C₁ * (n : ℝ) ^ 4) := by sorry

end GeomRescale
