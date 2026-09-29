-- Prove2me | Theorems.Thm_OnlineConvexOpt_ChangingEnv_dynamic_regret_bound
-- name    : OnlineConvexOpt.ChangingEnv.dynamic_regret_bound
-- status  : Disproved
-- author  : @mikedeng1
-- created : 2026-09-19T17:32:04.660985+00:00
-- url     : https://prove2.me/theorems/27b69c5f-8536-41b8-9973-0bb6585e1b40
-- title:
--   Theorem 10.1 — dynamic regret bound for OGD
-- statement:
--   **Statement (Theorem 10.1, p. 170, PDF p. 192).** Online gradient descent with step size
--   $\eta \approx \sqrt{P(u_1,\dots,u_T)/T}$ guarantees $\mathrm{DynamicRegret}_T(A,u_1,\dots,u_T)
--   = O(\sqrt{TP(u_1,\dots,u_T)})$.
--
--   A fixed comparator recovers the standard $O(\sqrt T)$ regret bound (path length $1$); in
--   general, OGD's dynamic regret degrades gracefully with how much the comparator itself
--   moves.
--
--   **Formalization Note.** The book's own step-size choice is only approximate
--   ("$\eta\approx\dots$"), so no crisp constant is committed to for the optimized bound;
--   instead this drafts the proof's own explicit, `η`-parametrized inequality
--   ($\mathrm{DynamicRegret}_T \le \frac{3D^2}{2\eta}P(u) + \frac\eta2 G^2T$, valid for every
--   $\eta>0$), which is exactly what the book proves before "the theorem now follows by choice
--   of `η`" — see `MODERATION_NOTES.md`. Reuses `FirstOrder.Protocol.IsOnlineGradientDescent`
--   with a constant step-size sequence.
-- source:
--   Hazan, Introduction to Online Convex Optimization, 2nd ed., arXiv:1909.05207v3, p. 170, Theorem 10.1 (PDF p. 192)

import Mathlib
import Definitions.Def_OnlineConvexOpt_ChangingEnv_Regret
import Definitions.Def_OnlineConvexOpt_FirstOrder_Protocol

open OnlineConvexOpt.FirstOrder

namespace OnlineConvexOpt.ChangingEnv

/-- Theorem 10.1 (Hazan, *Introduction to Online Convex Optimization*, 2nd ed.,
arXiv:1909.05207v3, p. 170, PDF p. 192). Online gradient descent (Algorithm 8) with a constant
step size `η > 0` guarantees, for every comparator sequence `u_1,...,u_T ∈ K`,
`DynamicRegret_T(A,u) ≤ (3D²/(2η)) P(u_1,...,u_T) + (η/2)G²T`.

This is the proof's own explicit inequality (Eq. before "The theorem now follows by choice of
η"), stated for an arbitrary `η > 0` rather than substituting the book's own only-approximate
optimal choice `η ≈ √(P/T)` (which yields the headline `O(√(TP))` but no explicit constant the
book itself commits to) — see `MODERATION_NOTES.md`. `K` (convex, nonempty, diameter `≤ D`) and
`f`, convex with subgradient norm `≤ G`, are this section's standing hypotheses (reused from
Chapter III), stated explicitly. -/
theorem dynamic_regret_bound
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (K : Set E) (hKconv : Convex ℝ K) (hKne : K.Nonempty)
    (D G : ℝ) (hDpos : 0 < D) (hGpos : 0 < G) (hD : ∀ x ∈ K, ∀ y ∈ K, dist x y ≤ D)
    (f : ℕ → E → ℝ) (hfconv : ∀ t, ConvexOn ℝ K (f t))
    (hfG : ∀ t, ∀ x ∈ K, ∀ v, HasGradientAt (f t) v x → ‖v‖ ≤ G)
    (η : ℝ) (hηpos : 0 < η)
    (u : ℕ → E) (hu : ∀ t, u t ∈ K)
    (x g : ℕ → E) (hOGD : IsOnlineGradientDescent K f (fun _ => η) x g)
    (T : ℕ) (hT : 1 ≤ T) :
    DynamicRegretT f x u T ≤ (3 * D ^ 2 / (2 * η)) * PathLength u T + (η / 2) * G ^ 2 * T := by sorry

end OnlineConvexOpt.ChangingEnv
