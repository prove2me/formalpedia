-- Prove2me | Theorems.Thm_OnlineConvexOpt_ChangingEnv_dynamic_regret_bound_v2
-- name    : OnlineConvexOpt.ChangingEnv.dynamic_regret_bound_v2
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-10-06T06:21:54.065385+00:00
-- url     : https://prove2.me/theorems/120ad8b4-48b3-4dca-877f-e79c16407839
-- title:
--   Theorem 10.1 — Dynamic regret of OGD, $(D^2+2D\,\mathrm{PathSum})/(2\eta)+\eta G^2T/2$ (corrected display)
-- statement:
--   **Statement (Theorem 10.1, explicit form).** Let $K$ be a nonempty convex set of diameter at most $D$ in a real Hilbert space and $f_0,f_1,\dots$ cost functions convex on $K$ with gradients of norm at most $G$ on $K$. Run online gradient descent (Algorithm 8) with a constant step size $\eta>0$. Then for every comparator sequence $u_0,\dots,u_{T-1}\in K$ and every $T\ge1$,
--   $$\mathrm{DynamicRegret}_T(u)=\sum_{t<T}f_t(x_t)-\sum_{t<T}f_t(u_t)\;\le\;\frac{D^2+2D\sum_{t<T-1}\|u_t-u_{t+1}\|}{2\eta}+\frac\eta2G^2T .$$
--   With $\eta\approx\sqrt{P/T}$ this is the book's headline $\mathrm{DynamicRegret}_T=O(\sqrt{T\,P(u)})$, $P(u)=\sum_t\|u_t-u_{t+1}\|+1$ the path length.
--
--   **Formalization Note.** The retired statement transcribed the final display of the book's proof, $\frac{3D^2}{2\eta}P(u)+\frac\eta2G^2T$. That display is not scale-invariant ($P$ adds a length to the constant $1$) and is false for $D<2/3$: the chain's step $D\sum\|u_{t-1}-u_t\|\le D^2\sum\|\dots\|$ silently assumes $D\ge1$. The statement here is the inequality the chain actually establishes (after halving) before that step: $2\sum_t\nabla_t^\top(x_t-u_t)\le\frac1\eta\bigl(\|x_1-u_1\|^2+\sum_{t\ge2}(\|x_t-u_t\|^2-\|x_t-u_{t-1}\|^2)\bigr)+\eta G^2T$ with $\|x_t-u_t\|^2-\|x_t-u_{t-1}\|^2\le2D\|u_t-u_{t-1}\|$. The path sum $\sum_{t<T-1}\|u_t-u_{t+1}\|$ equals `PathLength u T - 1`. Rounds are $0$-indexed; the standing assumptions on $K$ and $f$ are as in Chapter III. The file imports the `_v2` definition modules (`DynamicRegretT` is unchanged there).
-- source:
--   Hazan, Introduction to Online Convex Optimization, 2nd ed., arXiv:1909.05207v3, p. 170, Theorem 10.1 and its proof (PDF p. 192) — corrected transcription of the proof's final display, whose '3D²·P(u)/η' form silently assumes D ≥ 1

import Mathlib
import Definitions.Def_OnlineConvexOpt_ChangingEnv_Regret_v2
import Definitions.Def_OnlineConvexOpt_FirstOrder_Protocol_v2

open OnlineConvexOpt.FirstOrder

namespace OnlineConvexOpt.ChangingEnv

/-- Theorem 10.1 (Hazan, *Introduction to Online Convex Optimization*, 2nd ed.,
arXiv:1909.05207v3, p. 170, PDF p. 192), explicit form. Online gradient descent (Algorithm 8)
with a constant step size `η > 0` guarantees, for every comparator sequence `u_1,...,u_T ∈ K`,
`DynamicRegret_T(A,u) ≤ (D² + 2D Σ_{t=1}^{T-1} ‖u_t - u_{t+1}‖)/(2η) + (η/2) G² T`,
the inequality the book's proof establishes ("following the steps of the proof of Theorem
3.1"); with `η ≈ √(P/T)` this gives the headline `DynamicRegret_T = O(√(T·P(u_1,...,u_T)))`.
`K` (convex, nonempty, diameter `≤ D`) and `f`, convex with gradient norm `≤ G` on `K`, are
this section's standing hypotheses (reused from Chapter III), stated explicitly. In the
0-indexed convention the path sum is `Σ_{t < T-1} ‖u t - u (t+1)‖ = PathLength u T - 1`.

Corrected version: the retired statement transcribed the book's final display
`(3D²/(2η))·P(u) + (η/2)G²T` with `P(u) = Σ‖u_t - u_{t+1}‖ + 1`, which is not scale-invariant
(it adds a length to the constant `1`) and is false for `D < 2/3`: the step
`D·Σ‖u_{t-1} - u_t‖ ≤ D²·Σ‖…‖` in the book's chain silently assumes `D ≥ 1`. The bound stated
here is the one the chain actually proves, after halving, before that step. -/
theorem dynamic_regret_bound_v2
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (K : Set E) (hKconv : Convex ℝ K) (hKne : K.Nonempty)
    (D G : ℝ) (hDpos : 0 < D) (hGpos : 0 < G) (hD : ∀ x ∈ K, ∀ y ∈ K, dist x y ≤ D)
    (f : ℕ → E → ℝ) (hfconv : ∀ t, ConvexOn ℝ K (f t))
    (hfG : ∀ t, ∀ x ∈ K, ∀ v, HasGradientAt (f t) v x → ‖v‖ ≤ G)
    (η : ℝ) (hηpos : 0 < η)
    (u : ℕ → E) (hu : ∀ t, u t ∈ K)
    (x g : ℕ → E) (hOGD : IsOnlineGradientDescent K f (fun _ => η) x g)
    (T : ℕ) (hT : 1 ≤ T) :
    DynamicRegretT f x u T ≤
      (D ^ 2 + 2 * D * ∑ t ∈ Finset.range (T - 1), ‖u t - u (t + 1)‖) / (2 * η) +
        (η / 2) * G ^ 2 * T := by sorry

end OnlineConvexOpt.ChangingEnv
