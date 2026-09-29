-- Prove2me | Theorems.Thm_NonmonotoneSubmod_SmoothLS_phi_between_zero_opt
-- name    : NonmonotoneSubmod.SmoothLS.phi_between_zero_opt
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T21:10:07.324227+00:00
-- url     : https://prove2.me/theorems/acbfb01a-53df-4dde-83c5-cf8a049c447a
-- title:
--   §3.2, proof of Theorem 3.6 — $0 \le \Phi(A) \le OPT$
-- statement:
--   Let $f \ge 0$ be a set function on a finite ground set $X$ with $OPT = \max_{S \subseteq X} f(S)$, let $\delta \in [-1,1]$ and $A \subseteq X$. Then
--
--   $$
--   0 \le \Phi_\delta(A) = \mathbf{E}[f(\mathcal{R}(A,\delta))] \le OPT.
--   $$
--
--   Together with the increment identity for $\Phi$, this bounds the number of iterations of Algorithm SLS by $n^2/\delta$.
--
--   **Formalization Note** $\delta \in [-1,1]$ makes the inclusion probabilities lie in $[0,1]$ (the algorithm fixes $\delta \in [-1,1]$ in step 1).
-- source:
--   Feige, Mirrokni, Vondrák, Maximizing Non-Monotone Submodular Functions, SIAM J. Comput. 40(4), 2011, p. 1143, §3.2, proof of Theorem 3.6, sentence after the first display

import Mathlib
import Definitions.Def_NonmonotoneSubmod_Shared_OPT
import Definitions.Def_NonmonotoneSubmod_SmoothLS_BiasedSample

namespace NonmonotoneSubmod.SmoothLS

/-- §3.2, proof of Theorem 3.6, p. 1143 (Feige–Mirrokni–Vondrák 2011): "the value of `Φ(A)` is
always between `0` and `OPT`". For a nonnegative set function `f`, every bias `δ ∈ [-1, 1]` and
every `A ⊆ X`, `0 ≤ E[f(R(A, δ))] ≤ max_{S ⊆ X} f(S)`. -/
theorem phi_between_zero_opt {X : Type} [Fintype X] [DecidableEq X]
    (f : Finset X → ℝ) (hf0 : ∀ S, 0 ≤ f S) (δ : ℝ) (hδ0 : -1 ≤ δ) (hδ1 : δ ≤ 1)
    (A : Finset X) :
    0 ≤ Phi f δ A ∧ Phi f δ A ≤ NonmonotoneSubmod.Shared.OPT f := by sorry

end NonmonotoneSubmod.SmoothLS
