-- Prove2me | Theorems.Thm_KServer_potential_criterion
-- name    : KServer.potential_criterion
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-31T17:02:37.218581+00:00
-- url     : https://prove2.me/theorems/1892da11-1e95-42e0-b796-5cca947bdcd6
-- title:
--   Competitiveness from a potential with the offset and update properties
-- statement:
--   Fix an initial configuration $C_0$ and suppose a real number $\Phi_\sigma$ is assigned to every request sequence $\sigma$ — a *potential*. Suppose it satisfies
--
--   * the **offset property** (OP): $\Phi_\sigma + (C+1)\min_X w_\sigma(X) \ge 0$, and
--   * the **update property** (UP): for every request $s$ and every configuration $X$,
--     $$w_{\sigma s}(X) \;\le\; w_\sigma(X) + \bigl(\Phi_\sigma - \Phi_{\sigma s}\bigr),$$
--
--   where $w_\sigma$ is the work function after $\sigma$. Then there is a $C$-competitive online algorithm for $k$ servers starting from $C_0$.
--
--   ## Role
--
--   This is the standard amortisation step of the pseudocost method, and it is the bridge between the potential-function constructions of the work-function literature and a competitiveness statement. The quantity
--
--   $$r_s(w) \;=\; \max_X\bigl\{\,w^s(X) - w(X)\,\bigr\}$$
--
--   — the largest amount by which requesting $s$ can raise the work function — is called the *pseudocost* of the request. The pseudocost of a whole sequence dominates the cost of the Work Function Algorithm plus the optimum, so it suffices to show that the pseudocost is $(C+1)$-competitive. The update property says precisely that the potential pays for each step's pseudocost; summing over the sequence, the potential telescopes and
--
--   $$\sum_{t} r_{\sigma_t}(w_{t-1}) \;\le\; \Phi_{\varnothing} - \Phi_\sigma \;\le\; (C+1)\,\mathrm{opt}(\sigma) + \Phi_{\varnothing},$$
--
--   the last step being the offset property applied to a configuration nearly realising the optimum. Since $\Phi_\varnothing$ does not depend on $\sigma$, this is exactly a growth bound of the shape required by the extended cost lemma, and $C$-competitiveness follows.
--
--   The criterion reduces the analysis of a work-function algorithm to a purely local question about a single request, which is what makes potential constructions such as the lazy potential usable.
--
--   **Formalization note.** The update property is stated as an inequality over all configurations rather than through a maximum, so no attainment of $\max_X$ is needed. The offset property is likewise stated for every configuration; only its infimum over $X$ is used, and the passage from that infimum to the optimal offline cost is an $\varepsilon$-argument. The injective configuration $X_0$ and the hypothesis $1 \le k$ are what the extended cost lemma requires of the underlying space.
-- source:
--   W. Bein, M. Chrobak, L. Larmore, The 3-Server Problem in the Plane, Theoretical Computer Science 289(1) (2002) 335-354, Lemma 3: 'Let Phi_{w,r} be defined for each work function w with the last request r. Suppose Phi satisfies (OP) Phi_{w,r} + (C+1) min(w) >= 0 and (UP) if mu = w^s then Phi_{mu,s} + r_s(w) <= Phi_{w,r}. Then WFA is C-competitive on M.'

import Mathlib
import Definitions.Def_KServer_workfunctionU

namespace KServer

theorem potential_criterion (k : ℕ) (hk : 1 ≤ k) (M : Type) [MetricSpace M]
    (C₀ X₀ : Config k M) (hX₀ : Function.Injective X₀) (C : ℝ) (hC : 0 ≤ C)
    (Φ : List M → ℝ)
    (hOP : ∀ (τ : List M) (X : Config k M), 0 ≤ Φ τ + (C + 1) * workFnU C₀ τ X)
    (hUP : ∀ (τ : List M) (s : M) (X : Config k M), Function.Injective X →
      workFnU C₀ (τ ++ [s]) X ≤ workFnU C₀ τ X + (Φ τ - Φ (τ ++ [s]))) :
    ∃ A : OnlineAlgorithm k M, A.conf [] = C₀ ∧ IsCompetitive A C := by sorry

end KServer
