-- Prove2me | Theorems.Thm_NonmonotoneSubmod_SmoothLS_phi_increment
-- name    : NonmonotoneSubmod.SmoothLS.phi_increment
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T21:09:33.453918+00:00
-- url     : https://prove2.me/theorems/49b51680-7941-4aca-9831-d6791bc5e863
-- title:
--   §3.2, proof of Theorem 3.6 — one step changes $\Phi$ by $\pm\delta\,\omega_{A,\delta}(x)$
-- statement:
--   Let $f$ be a real set function on a finite ground set $X$, $\delta \in \mathbb{R}$, $A \subseteq X$, $x \in X$, and write $\Phi_\delta(A) = \mathbf{E}[f(\mathcal{R}(A,\delta))]$. Then:
--
--   1. if $x \notin A$,
--   $$
--   \Phi_\delta(A \cup \{x\}) - \Phi_\delta(A) = \delta\, \omega_{A,\delta}(x);
--   $$
--   2. if $x \in A$,
--   $$
--   \Phi_\delta(A \setminus \{x\}) - \Phi_\delta(A) = -\delta\, \omega_{A,\delta}(x).
--   $$
--
--   Moving $x$ into or out of $A$ changes only its own inclusion probability, from $q$ to $p$ or back, and the potential changes by $(p-q) = \delta$ times the smoothed marginal value of $x$. This is why every iteration of Algorithm SLS increases $\Phi$ by more than $\frac{\delta}{n^2} OPT$.
--
--   **Formalization Note** The identity is algebraic and holds for every real $\delta$ and every real $f$; no submodularity or sign is assumed. The second part is the page's "Similarly, executing step 4 …", stated as an identity.
-- source:
--   Feige, Mirrokni, Vondrák, Maximizing Non-Monotone Submodular Functions, SIAM J. Comput. 40(4), 2011, p. 1143, §3.2, proof of Theorem 3.6, first display and the sentence following it

import Mathlib
import Definitions.Def_NonmonotoneSubmod_SmoothLS_BiasedSample

namespace NonmonotoneSubmod.SmoothLS

/-- §3.2, proof of Theorem 3.6, p. 1143, first display (Feige–Mirrokni–Vondrák 2011). For every
real set function `f`, every bias `δ`, every `A ⊆ X` and every element `x`, with
`Φ_δ(A) = E[f(R(A, δ))]`:
* if `x ∉ A` (step 3 adds `x`), then `Φ_δ(A ∪ {x}) - Φ_δ(A) = δ ω_{A,δ}(x)`;
* if `x ∈ A` (step 4 removes `x`), then `Φ_δ(A \ {x}) - Φ_δ(A) = -δ ω_{A,δ}(x)`. -/
theorem phi_increment {X : Type} [Fintype X] [DecidableEq X]
    (f : Finset X → ℝ) (δ : ℝ) (A : Finset X) (x : X) :
    (x ∉ A → Phi f δ (insert x A) - Phi f δ A = δ * omegaB f A δ x) ∧
    (x ∈ A → Phi f δ (A.erase x) - Phi f δ A = -(δ * omegaB f A δ x)) := by sorry

end NonmonotoneSubmod.SmoothLS
