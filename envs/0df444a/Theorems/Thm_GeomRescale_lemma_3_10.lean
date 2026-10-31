-- Prove2me | Theorems.Thm_GeomRescale_lemma_3_10
-- name    : GeomRescale.lemma_3_10
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:20:40.202021+00:00
-- url     : https://prove2.me/theorems/b65c9cf7-b548-439f-998f-0d847ac8e31a
-- title:
--   Lemma 3.10: $F_\mu \subseteq E(R)$
-- statement:
--   Throughout Algorithm Rescaling-SFM, $F_\mu \subseteq E(R)$ holds, for the current $\mu$ and $R$.
--
--   The ellipsoid therefore confines the feasible region, while its volume shrinks by Lemma 3.12.
--
--   Differences from the source:
--   - encoding: throughout the algorithm / at every stage → every state reachable from the initial state, for $f, \Lambda$ as in the goal; reason: a run is a relation, so this covers all tie-breaks and argmins; the placeholder $\mu, W$ of the state before lines 2–3 is included, and the statement holds there too
--   - encoding: a ground set $V$ with $n = |V|$ elements → `1 ≤ n`; reason: the parameter $\varepsilon = 1/(20n)$ of Algorithm 2 is undefined at $n = 0$; the hypothesis excludes only that case
--   - generalization: the run of Algorithm 2 with $T = 5n\log(nL_{f,2})$ → the runs for every $\Lambda \ge L_{f,2}$, with $T = \lceil 5n\log_2(n\Lambda)\rceil_+$; reason: $\Lambda = L_{f,2}$ gives the paper's run, with $T$ rounded as in Theorem 3.6; the statement holds on every such run
--   - reading: $g/\|g\|_Q$ with no case for $g = 0$ → $g/\|g\|_Q := 0$ at $g = 0$ in the step relation; reason: $g = 0$ occurs (for $f \equiv 0$ at line 2 of Algorithm 1), and the run needs a value there
--   - reading: $g_1, \dots, g_k$ in (10) and in line 8 of Algorithm 2, returned after line 15 of Algorithm 1 incremented $k$ → $g_1, \dots, g_{k-1}$, the bases the call computed; reason: line 15 has incremented $k$, so no $g_k$ was computed
-- source:
--   Dadush, Végh & Zambelli, Geometric Rescaling Algorithms for Submodular Function Minimization, arXiv:1707.05065v4, Lemma 3.10, p.11, and Lemma A.1, p.31

import Mathlib
import Definitions.Def_NonmonotoneSubmod_Shared_Submodular
import Definitions.Def_GeomRescale_fR
import Definitions.Def_GeomRescale_Ltwo
import Definitions.Def_GeomRescale_Reachable
import Definitions.Def_GeomRescale_ellipsoid
import Definitions.Def_GeomRescale_Fmu

open NonmonotoneSubmod.Shared
open SchrijverSFM.Alg

namespace GeomRescale

/-- Lemma 3.10 (Dadush, Végh & Zambelli, Geometric Rescaling Algorithms for Submodular Function Minimization, arXiv:1707.05065v4, Lemma 3.10, p.11, proved with Lemma A.1, p.31): throughout Algorithm
Rescaling-SFM, `F_μ ⊆ E(R)` holds.

**Formalization Note.** "Throughout" is every reachable state, with the current `μ` and `R`. -/
theorem lemma_3_10 {n : ℕ} (hn : 1 ≤ n) (f : Finset (Fin n) → ℤ) (hsub : Submodular (fR f))
    (hf0 : f ∅ = 0) (Λ : ℝ) (hΛ : Ltwo (fR f) ≤ Λ) (s : St n) (hs : Reachable f Λ s) :
    Fmu (fR f) (s.vn.μ : ℝ) ⊆ ellipsoid s.R := by sorry

end GeomRescale
