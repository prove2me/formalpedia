-- Prove2me | Theorems.Thm_GeomRescale_lemma_3_11
-- name    : GeomRescale.lemma_3_11
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:21:55.476692+00:00
-- url     : https://prove2.me/theorems/43c51c7a-09a2-4b45-9907-0b0c03b66b13
-- title:
--   Lemma 3.11: $\|x\|_Q \ge \omega_\mu \|x\|_2$
-- statement:
--   Throughout Algorithm Rescaling-SFM, $\|x\|_Q \ge \omega_\mu \|x\|_2$ holds for every $x \in B(f) \setminus \{0\}$, and also for every $x \in B(f_\mu) \setminus \{0\}$.
--
--   This links the geometry of $Q$ to the condition number.
--
--   Differences from the source:
--   - generalization: $x \in B(f) \setminus \{0\}$ → both $x \in B(f) \setminus \{0\}$ and $x \in B(f_\mu) \setminus \{0\}$; reason: the printed proof reads the definition of $\omega_\mu$ on $B(f_\mu)$ and Theorem 3.6 applies it there; both forms are true
--   - reading: $\omega_\mu$ as a minimum → `sInf`, which is $0$ if $B(f_\mu) = \{0\}$; reason: $B(f_\mu) \setminus \{0\}$ may be empty or not closed here
--   - encoding: throughout the algorithm / at every stage → every state reachable from the initial state, for $f, \Lambda$ as in the goal; reason: a run is a relation, so this covers all tie-breaks and argmins; the placeholder $\mu, W$ of the state before lines 2–3 is included, and the statement holds there too
--   - encoding: a ground set $V$ with $n = |V|$ elements → `1 ≤ n`; reason: the parameter $\varepsilon = 1/(20n)$ of Algorithm 2 is undefined at $n = 0$; the hypothesis excludes only that case
--   - generalization: the run of Algorithm 2 with $T = 5n\log(nL_{f,2})$ → the runs for every $\Lambda \ge L_{f,2}$, with $T = \lceil 5n\log_2(n\Lambda)\rceil_+$; reason: $\Lambda = L_{f,2}$ gives the paper's run, with $T$ rounded as in Theorem 3.6; the statement holds on every such run
--   - reading: $g/\|g\|_Q$ with no case for $g = 0$ → $g/\|g\|_Q := 0$ at $g = 0$ in the step relation; reason: $g = 0$ occurs (for $f \equiv 0$ at line 2 of Algorithm 1), and the run needs a value there
--   - reading: $g_1, \dots, g_k$ in (10) and in line 8 of Algorithm 2, returned after line 15 of Algorithm 1 incremented $k$ → $g_1, \dots, g_{k-1}$, the bases the call computed; reason: line 15 has incremented $k$, so no $g_k$ was computed
-- source:
--   Dadush, Végh & Zambelli, Geometric Rescaling Algorithms for Submodular Function Minimization, arXiv:1707.05065v4, Lemma 3.11, p.12

import Mathlib
import Definitions.Def_NonmonotoneSubmod_Shared_Submodular
import Definitions.Def_SchrijverSFM_Alg_Setting
import Definitions.Def_GeomRescale_fR
import Definitions.Def_GeomRescale_enlarge
import Definitions.Def_GeomRescale_norm2
import Definitions.Def_GeomRescale_qnorm
import Definitions.Def_GeomRescale_Ltwo
import Definitions.Def_GeomRescale_Reachable
import Definitions.Def_GeomRescale_omega

open NonmonotoneSubmod.Shared
open SchrijverSFM.Alg

namespace GeomRescale

/-- Lemma 3.11 (Dadush, Végh & Zambelli, Geometric Rescaling Algorithms for Submodular Function Minimization, arXiv:1707.05065v4, Lemma 3.11, p.12): throughout Algorithm Rescaling-SFM,
`‖x‖_Q ≥ ω_μ ‖x‖₂` for every `x ∈ B(f) ∖ {0}`, and also for every `x ∈ B(f_μ) ∖ {0}`.

**Formalization Note.** The page prints `B(f)`, but its proof closes "from the definition of `ω_μ`",
which ranges over `B(f_μ)`, and the proof of Theorem 3.6 applies the lemma to `g_h ∈ B(f_μ)`. Both
forms are true and both are stated. -/
theorem lemma_3_11 {n : ℕ} (hn : 1 ≤ n) (f : Finset (Fin n) → ℤ) (hsub : Submodular (fR f))
    (hf0 : f ∅ = 0) (Λ : ℝ) (hΛ : Ltwo (fR f) ≤ Λ) (s : St n) (hs : Reachable f Λ s) :
    (∀ x ∈ baseB (fR f) \ {0},
      omega (fR f) (s.vn.μ : ℝ) * norm2 x ≤ qnorm s.Q x) ∧
      ∀ x ∈ baseB (enlarge (fR f) (s.vn.μ : ℝ)) \ {0},
        omega (fR f) (s.vn.μ : ℝ) * norm2 x ≤ qnorm s.Q x := by sorry

end GeomRescale
