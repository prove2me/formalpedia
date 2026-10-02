-- Prove2me | Theorems.Thm_HunterPDE_Hyperbolic_weak_continuity
-- name    : HunterPDE.Hyperbolic.weak_continuity
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T00:36:22.401861+00:00
-- url     : https://prove2.me/theorems/b33db47d-0bcd-4731-a2f7-90f028f28ad1
-- title:
--   Lemma 7.8 — L^∞(0,T;𝒱) with u_t ∈ L²(0,T;ℋ) implies u ∈ C_w([0,T];𝒱)
-- statement:
--   Let $\mathcal{V}, \mathcal{H}$ be real Hilbert spaces with $\mathcal{V} \hookrightarrow \mathcal{H}$ densely and continuously embedded, and let $T > 0$. If
--   $$u \in L^\infty(0,T;\mathcal{V}), \qquad u_t \in L^2(0,T;\mathcal{H}),$$
--   then $u \in C_w([0,T];\mathcal{V})$ is weakly continuous.
--
--   The lemma turns the uniform-in-time bounds produced by energy estimates into pointwise-in-time information, and gives the weak continuity of the Galerkin limit in $H^1_0$ and of its velocity in $L^2$.
--
--   **Formalization Note.** The embedding is a bounded, injective linear map $\iota$ with dense range; $u_t$ is the weak time derivative of $\iota\circ u$. Since $u$ is an $L^\infty$ class, the conclusion is that $u$ agrees a.e. on $(0,T)$ with a function $\tilde u$ such that $t\mapsto \ell(\tilde u(t))$ is continuous on $[0,T]$ for every $\ell \in \mathcal{V}'$.
-- source:
--   Hunter, Notes on Partial Differential Equations (revised 6/18/2014), p. 217, Lemma 7.8

import Mathlib
import Definitions.Def_HunterPDE_Hyperbolic_WeakTimeDeriv

namespace HunterPDE.Hyperbolic

open MeasureTheory Set

/-- Lemma 7.8 (Hunter, p. 217). Let `𝒱, ℋ` be real Hilbert spaces with `𝒱 ↪ ℋ` densely and
continuously embedded (`ι` injective, bounded, with dense range). If `u ∈ L^∞(0, T; 𝒱)` and
its weak time derivative (taken in `ℋ`) satisfies `u_t ∈ L²(0, T; ℋ)`, then `u ∈ C_w([0, T]; 𝒱)`:
`u` agrees a.e. on `(0, T)` with a function `ũ : [0, T] → 𝒱` such that `t ↦ ⟨ℓ, ũ(t)⟩` is
continuous on `[0, T]` for every `ℓ ∈ 𝒱'`. -/
theorem weak_continuity {V H : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [CompleteSpace V] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (ι : V →L[ℝ] H) (hι : Function.Injective ι) (hdense : DenseRange ι)
    (T : ℝ) (hT : 0 < T) (u : ℝ → V) (u_t : ℝ → H)
    (hu : MemLp u ⊤ (volume.restrict (Ioo 0 T)))
    (hut : MemLp u_t 2 (volume.restrict (Ioo 0 T)))
    (hder : HasWeakTimeDeriv T (fun t => ι (u t)) u_t) :
    ∃ ũ : ℝ → V, ũ =ᵐ[volume.restrict (Ioo 0 T)] u ∧ WeaklyContinuousOn T ũ := by sorry

end HunterPDE.Hyperbolic
