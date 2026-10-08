-- Prove2me | Theorems.Thm_GlobalInexactNewton_Backtracking_inb_isMRRun
-- name    : GlobalInexactNewton.Backtracking.inb_isMRRun
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T09:35:41.491801+00:00
-- url     : https://prove2.me/theorems/b4382854-7c93-465b-828c-fddf9072d30b
-- title:
--   §6, p. 410 — Algorithm INB is Algorithm MR with the backtracking curve (6.1)
-- statement:
--   Let $E$ be a real normed space and $F:E\to E$. Consider a run of Algorithm INB with initial levels $\bar\eta_k$ and initial inexact Newton steps $\bar s_k$, and define the backtracking curve
--   $$\sigma_k(\eta)=\frac{1-\eta}{1-\bar\eta_k}\,\bar s_k,\qquad\bar\eta_k\le\eta\le1. \tag{6.1}$$
--   Then:
--
--   1. the same data, with $\sigma_k$ in place of the curves, is a run of Algorithm MR (in particular $\sigma_k$ satisfies (5.1));
--   2. every step visited by the while-loop of Algorithm INB is $\sigma_k$ at the corresponding level: if the loop has produced $s_k$ and $\eta_k$ after any number of passes, then $s_k=\sigma_k(\eta_k)$.
--
--   This identification is how Theorem 6.1 for INB is derived from Theorem 5.2 for MR.
--
--   **Formalization Note** Part 2 is stated for every loop index $j$: $s^{(j)}=\frac{1-\eta^{(j)}}{1-\bar\eta_k}\bar s_k$. No differentiability or finite dimension is needed, so neither is assumed.
-- source:
--   Eisenstat and Walker, Globally Convergent Inexact Newton Methods, SIAM J. Optim. 4(2) (1994), §6, after (6.1), p. 410

import Mathlib
import Definitions.Def_GlobalInexactNewton_Backtracking_Method
open Filter Topology

namespace GlobalInexactNewton.Backtracking

/-- Eisenstat–Walker (1994), §6, after (6.1), p. 410: Algorithm INB is a special case of
Algorithm MR. With the backtracking curve (6.1) `σ_k(η) = ((1 - η)/(1 - η̄_k)) s̄_k`, every run of
Algorithm INB is a run of Algorithm MR with the same data, and every step visited by the
while-loop is `σ_k` at the corresponding level: `s_k = σ_k(η_k)` throughout the loop. -/
theorem inb_isMRRun {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : E → E) (ηmax t θmin θmax : ℝ) (x : ℕ → E) (ηbar : ℕ → ℝ) (sbar : ℕ → E)
    (θ : ℕ → ℕ → ℝ) (m : ℕ → ℕ) (hrun : IsINBRun F ηmax t θmin θmax x ηbar sbar θ m) :
    IsMRRun F ηmax t θmin θmax x ηbar (fun k η => ((1 - η) / (1 - ηbar k)) • sbar k) θ m ∧
      ∀ k j, trialStep (sbar k) (θ k) j =
        ((1 - trialLevel (ηbar k) (θ k) j) / (1 - ηbar k)) • sbar k := by sorry

end GlobalInexactNewton.Backtracking
