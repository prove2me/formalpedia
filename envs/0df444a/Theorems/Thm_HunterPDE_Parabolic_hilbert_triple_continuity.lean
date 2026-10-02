-- Prove2me | Theorems.Thm_HunterPDE_Parabolic_hilbert_triple_continuity
-- name    : HunterPDE.Parabolic.hilbert_triple_continuity
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T00:19:14.374997+00:00
-- url     : https://prove2.me/theorems/f92582a8-e271-4ae5-b3af-83f2c4e3b7d7
-- title:
--   Theorem 6.41 — u ∈ L²(0,T;𝒱), u_t ∈ L²(0,T;𝒱′) ⇒ u ∈ C([0,T];ℋ), with (6.45)–(6.47)
-- statement:
--   Let $\mathcal{V} \hookrightarrow \mathcal{H} \hookrightarrow \mathcal{V}'$ be a Hilbert triple and $T > 0$. If $u \in L^2(0,T;\mathcal{V})$ and its weak time derivative, taken in $\mathcal{V}'$, satisfies $u_t \in L^2(0,T;\mathcal{V}')$, then $u \in C([0,T];\mathcal{H})$, i.e. $u$ agrees a.e. on $(0,T)$ with a continuous $\tilde u : [0,T] \to \mathcal{H}$. Moreover:
--   (1) for every $v \in \mathcal{V}$, $t \mapsto (u(t), v)_{\mathcal{H}}$ is weakly differentiable in $(0,T)$ and $\frac{d}{dt}(u(t), v)_{\mathcal{H}} = \langle u_t(t), v\rangle$;
--   (2) $t \mapsto \|u(t)\|^2_{\mathcal{H}}$ is weakly differentiable in $(0,T)$ and $\frac{d}{dt}\|u\|^2_{\mathcal{H}} = 2\langle u_t, u\rangle$;
--   (3) there is a constant $C = C(T)$ with
--   $$\|u\|_{L^\infty(0,T;\mathcal{H})} \le C\big(\|u\|_{L^2(0,T;\mathcal{V})} + \|u_t\|_{L^2(0,T;\mathcal{V}')}\big).$$
--
--   This is what gives the initial condition $u(0) = g$ of a weak parabolic solution a meaning, and (6.46) is the energy identity behind uniqueness.
--
--   **Formalization Note.** Weak differentiability in (1)–(2) is (6.14) for real functions. $C$ is quantified after the triple and $T$ and before $u$; it cannot be independent of the triple, since rescaling the norm of $\mathcal{V}$ changes the right-hand side and not the left. Norms are `eLpNorm` on $(0,T)$ in $[0,\infty]$, with $C \ge 0$ finite.
-- source:
--   Hunter, Notes on Partial Differential Equations (revised 6/18/2014), p. 208, Theorem 6.41

import Mathlib
import Definitions.Def_HunterPDE_Parabolic_WeakTimeDeriv
import Definitions.Def_HunterPDE_Parabolic_HilbertTriple

open MeasureTheory
open scoped ENNReal NNReal

namespace HunterPDE.Parabolic

/-- Theorem 6.41 of Hunter, *Notes on PDEs* (revised 6/18/2014), p. 208: let `𝒱 ↪ ℋ ↪ 𝒱'` be a
Hilbert triple and `T > 0`. If `u ∈ L²(0, T; 𝒱)` and its weak time derivative (6.14), taken in
`𝒱'`, satisfies `u_t ∈ L²(0, T; 𝒱')`, then `u ∈ C([0, T]; ℋ)`: there is a continuous
`ũ : [0, T] → ℋ` equal to `u(t)` for a.e. `t ∈ (0, T)`. Moreover
(1) for every `v ∈ 𝒱`, `t ↦ (u(t), v)_ℋ` is weakly differentiable in `(0, T)` with
`d/dt (u(t), v)_ℋ = ⟨u_t(t), v⟩` (6.45);
(2) `t ↦ ‖u(t)‖²_ℋ` is weakly differentiable in `(0, T)` with `d/dt ‖u‖²_ℋ = 2⟨u_t, u⟩` (6.46);
(3) there is a constant `C = C(T)` with
`‖u‖_{L^∞(0,T;ℋ)} ≤ C (‖u‖_{L²(0,T;𝒱)} + ‖u_t‖_{L²(0,T;𝒱')})` (6.47).
The constant is quantified after the triple and `T` and before `u`: it cannot be independent of
the triple (rescaling the norm of `𝒱` changes the right-hand side but not the left). -/
theorem hilbert_triple_continuity {V H : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [CompleteSpace V] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (HT : HilbertTriple V H) (T : ℝ) (hT : 0 < T) :
    ∃ C : ℝ≥0, ∀ (u : ℝ → V) (ut : ℝ → StrongDual ℝ V),
      MemLp u 2 (volume.restrict (Set.Ioo 0 T)) →
      MemLp ut 2 (volume.restrict (Set.Ioo 0 T)) →
      HasWeakTimeDeriv HT.toDualV T u ut →
      ∃ ũ : ℝ → H, ContinuousOn ũ (Set.Icc 0 T) ∧
        (∀ᵐ t ∂(volume.restrict (Set.Ioo 0 T)), ũ t = HT.toH (u t)) ∧
        (∀ v : V, HasWeakTimeDeriv (ContinuousLinearMap.id ℝ ℝ) T
          (fun t => inner ℝ (ũ t) (HT.toH v)) (fun t => ut t v)) ∧
        HasWeakTimeDeriv (ContinuousLinearMap.id ℝ ℝ) T
          (fun t => ‖ũ t‖ ^ 2) (fun t => 2 * ut t (u t)) ∧
        eLpNorm ũ ∞ (volume.restrict (Set.Ioo 0 T)) ≤
          (C : ℝ≥0∞) * (eLpNorm u 2 (volume.restrict (Set.Ioo 0 T)) +
            eLpNorm ut 2 (volume.restrict (Set.Ioo 0 T))) := by sorry

end HunterPDE.Parabolic
