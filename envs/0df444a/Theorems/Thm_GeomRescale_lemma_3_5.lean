-- Prove2me | Theorems.Thm_GeomRescale_lemma_3_5
-- name    : GeomRescale.lemma_3_5
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:18:47.456036+00:00
-- url     : https://prove2.me/theorems/03fd47ef-108e-47f4-9d4f-95beb774d8d3
-- title:
--   Lemma 3.5: Algorithm 1 terminates with a correct output
-- statement:
--   Let $f$ be an integer valued submodular function with $f(\emptyset) = 0$, $\mu \ge \max\{0, -f(V)\}$ an integer, $W \subseteq V$ with $f(W) = -\mu$, $Q$ symmetric positive definite, and $\varepsilon > 0$. For every vertex chosen at line 2:
--
--   1. every state reached with $\|y\|_Q > \varepsilon$ has a next iteration;
--   2. every sequence of iterations has length at most $\lceil 1/\varepsilon^2 \rceil$;
--   3. every state reached with $\|y\|_Q \le \varepsilon$ satisfies the Output list of Algorithm 1.
--
--   So Algorithm 1 terminates in $\lceil 1/\varepsilon^2 \rceil$ iterations, returning a correct output.
--
--   Differences from the source:
--   - reading: $g/\|g\|_Q$ with no case for $g = 0$ → $g/\|g\|_Q := 0$ at $g = 0$; reason: $g = 0$ occurs (for $f \equiv 0$ at line 2); the output identity keeps its form
--   - reading: return $g_1, \dots, g_k$ after line 15 → $g_1, \dots, g_{k-1}$; reason: line 15 has incremented $k$
--   - encoding: an arbitrary vertex of $B(f_\mu)$ → the greedy vector of an arbitrary order; reason: every vertex has this form, p.4
-- source:
--   Dadush, Végh & Zambelli, Geometric Rescaling Algorithms for Submodular Function Minimization, arXiv:1707.05065v4, Lemma 3.5, p.9

import Mathlib
import Definitions.Def_NonmonotoneSubmod_Shared_Submodular
import Definitions.Def_GeomRescale_fR
import Definitions.Def_GeomRescale_qnorm
import Definitions.Def_GeomRescale_vnStart
import Definitions.Def_GeomRescale_VNStep
import Definitions.Def_GeomRescale_IsCorrectOutput

open NonmonotoneSubmod.Shared
open SchrijverSFM.Alg

namespace GeomRescale

/-- Lemma 3.5 (Dadush, Végh & Zambelli, Geometric Rescaling Algorithms for Submodular Function Minimization, arXiv:1707.05065v4, Lemma 3.5, p.9): Algorithm 1 terminates in `⌈1/ε²⌉` iterations, returning a
correct output. For every input of p.8 and every order `σ` chosen at line 2:

1. a state with `‖y‖_Q > ε` always has a next iteration;
2. every sequence of iterations has length at most `⌈1/ε²⌉`;
3. every state with `‖y‖_Q ≤ ε` satisfies the Output list of p.8.

**Formalization Note.** `IsCorrectOutput` is that list, with `g_i/‖g_i‖_Q := 0` at `g_i = 0`. Clause 2
counts iterations of lines 5–15. `e`, `o` are the counters on entry. -/
theorem lemma_3_5 {n : ℕ} (f : Finset (Fin n) → ℤ) (hsub : Submodular (fR f)) (hf0 : f ∅ = 0)
    (μ : ℤ) (hμ : max 0 (-f Finset.univ) ≤ μ) (W : Finset (Fin n)) (hW : f W = -μ)
    (Q : Matrix (Fin n) (Fin n) ℝ) (hQ : Q.PosDef) (ε : ℝ) (hε : 0 < ε)
    (σ : Equiv.Perm (Fin n)) (e o : ℕ) :
    (∀ v, Relation.ReflTransGen (VNStep f Q ε) (vnStart f μ W Q σ e o) v →
      ε < qnorm Q v.y → ∃ v', VNStep f Q ε v v') ∧
      (∀ l : List (VN n), (vnStart f μ W Q σ e o :: l).IsChain (VNStep f Q ε) →
        l.length ≤ ⌈1 / ε ^ 2⌉₊) ∧
      (∀ v, Relation.ReflTransGen (VNStep f Q ε) (vnStart f μ W Q σ e o) v →
        qnorm Q v.y ≤ ε → IsCorrectOutput f Q ε μ v) := by sorry

end GeomRescale
