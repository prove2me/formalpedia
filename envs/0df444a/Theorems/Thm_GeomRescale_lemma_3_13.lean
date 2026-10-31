-- Prove2me | Theorems.Thm_GeomRescale_lemma_3_13
-- name    : GeomRescale.lemma_3_13
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:21:20.398989+00:00
-- url     : https://prove2.me/theorems/a291a9e0-ef74-4003-8b1e-8f962f3ee262
-- title:
--   Lemma 3.13 (corrected: $\Gamma \neq \emptyset$): a base of small $Q$-norm
-- statement:
--   At any stage of Algorithm Rescaling-SFM with $\Gamma \neq \emptyset$, there exists a point $\bar g \in \Gamma$ such that
--
--   $$\|\bar g\|_Q \sqrt{\det(R)^{1/n} - 1} \le \|\bar g\|_2.$$
--
--   Combined with Lemmas 3.11 and 3.12, this forces $\omega_\mu$ below the bound of Lemma 3.8 after $T$ rescalings.
--
--   Differences from the source:
--   - correction: at any stage → at any stage with $\Gamma \neq \emptyset$; reason: $\Gamma = \emptyset$ at line 1 of Algorithm 2 for every $f$, so no $\bar g \in \Gamma$ exists; the proof's argmin over $\Gamma$ and the use in Theorem 3.6 need $\Gamma \neq \emptyset$
--   - encoding: throughout the algorithm / at every stage → every state reachable from the initial state, for $f, \Lambda$ as in the goal; reason: a run is a relation, so this covers all tie-breaks and argmins; the placeholder $\mu, W$ of the state before lines 2–3 is included, and the statement holds there too
--   - encoding: a ground set $V$ with $n = |V|$ elements → `1 ≤ n`; reason: the parameter $\varepsilon = 1/(20n)$ of Algorithm 2 is undefined at $n = 0$; the hypothesis excludes only that case
--   - generalization: the run of Algorithm 2 with $T = 5n\log(nL_{f,2})$ → the runs for every $\Lambda \ge L_{f,2}$, with $T = \lceil 5n\log_2(n\Lambda)\rceil_+$; reason: $\Lambda = L_{f,2}$ gives the paper's run, with $T$ rounded as in Theorem 3.6; the statement holds on every such run
--   - reading: $g/\|g\|_Q$ with no case for $g = 0$ → $g/\|g\|_Q := 0$ at $g = 0$ in the step relation; reason: $g = 0$ occurs (for $f \equiv 0$ at line 2 of Algorithm 1), and the run needs a value there
--   - reading: $g_1, \dots, g_k$ in (10) and in line 8 of Algorithm 2, returned after line 15 of Algorithm 1 incremented $k$ → $g_1, \dots, g_{k-1}$, the bases the call computed; reason: line 15 has incremented $k$, so no $g_k$ was computed
-- source:
--   Dadush, Végh & Zambelli, Geometric Rescaling Algorithms for Submodular Function Minimization, arXiv:1707.05065v4, Lemma 3.13, p.12, proof p.32

import Mathlib
import Definitions.Def_NonmonotoneSubmod_Shared_Submodular
import Definitions.Def_GeomRescale_fR
import Definitions.Def_GeomRescale_norm2
import Definitions.Def_GeomRescale_qnorm
import Definitions.Def_GeomRescale_Ltwo
import Definitions.Def_GeomRescale_Reachable

open NonmonotoneSubmod.Shared
open SchrijverSFM.Alg

namespace GeomRescale

/-- Lemma 3.13, corrected (Dadush, Végh & Zambelli, Geometric Rescaling Algorithms for Submodular Function Minimization, arXiv:1707.05065v4, Lemma 3.13, p.12, proof p.32): at any stage of Algorithm
Rescaling-SFM with `Γ ≠ ∅`, there exists a point `ḡ ∈ Γ` such that
`‖ḡ‖_Q √(det(R)^{1/n} − 1) ≤ ‖ḡ‖₂`.

**Formalization Note.** The page says "at any stage", but `Γ = ∅` until the first rescaling, so no
`ḡ` exists there. The appendix proof takes an argmin over `Γ`, and the proof of Theorem 3.6 applies
the lemma after `T ≥ 1` rescalings. `det(R) ≥ 1` along a run, so the square root is of a nonnegative
number. -/
theorem lemma_3_13 {n : ℕ} (hn : 1 ≤ n) (f : Finset (Fin n) → ℤ) (hsub : Submodular (fR f))
    (hf0 : f ∅ = 0) (Λ : ℝ) (hΛ : Ltwo (fR f) ≤ Λ) (s : St n) (hs : Reachable f Λ s)
    (hΓ : s.Γ ≠ []) :
    ∃ g ∈ s.Γ, qnorm s.Q g * √(s.R.det ^ (1 / (n : ℝ)) - 1) ≤ norm2 g := by sorry

end GeomRescale
