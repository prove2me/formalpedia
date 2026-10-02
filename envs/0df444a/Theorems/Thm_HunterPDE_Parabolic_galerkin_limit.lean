-- Prove2me | Theorems.Thm_HunterPDE_Parabolic_galerkin_limit
-- name    : HunterPDE.Parabolic.galerkin_limit
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T00:23:55.785976+00:00
-- url     : https://prove2.me/theorems/0ffd4bb2-12b0-42bc-bac4-78a6545a5c78
-- title:
--   Proposition 6.7 — a subsequence of Galerkin approximations converges weakly to a weak solution
-- statement:
--   Under Assumption 6.1, let $u_N$ ($N \in \mathbb{N}$) be the approximate solutions of Definition 6.4 for data $f \in L^2(0,T;H^{-1}(\Omega))$, $g \in L^2(\Omega)$. A subsequence $u_{N_k}$ converges weakly to a weak solution
--   $$u \in C([0,T];L^2(\Omega)) \cap L^2(0,T;H^1_0(\Omega))$$
--   of $u_t + Lu = f$, $u = 0$ on $\partial\Omega$, $u(0) = g$ (Definition 6.2), with $u_t \in L^2(0,T;H^{-1}(\Omega))$. Moreover there is a constant $C$ such that
--   $$\|u\|_{L^\infty(0,T;L^2)} + \|u\|_{L^2(0,T;H^1_0)} + \|u_t\|_{L^2(0,T;H^{-1})} \le C\big(\|f\|_{L^2(0,T;H^{-1})} + \|g\|_{L^2}\big).$$
--
--   This is the existence half of Theorem 6.3.
--
--   **Formalization Note.** Weak convergence is written out as on p. 186, with both convergences the proof establishes: $\int_0^T \langle F, u_{N_k}\rangle\,dt \to \int_0^T \langle F, u\rangle\,dt$ for every $F \in L^2(0,T;H^{-1})$ ($u_{N_k} \rightharpoonup u$ in $L^2(0,T;H^1_0)$), and $\int_0^T \langle u_{N_k t}, v\rangle\,dt \to \int_0^T \langle u_t, v\rangle\,dt$ for every $v \in L^2(0,T;H^1_0)$ ($u_{N_k t} \rightharpoonup u_t$ in $L^2(0,T;H^{-1})$). The first implies the printed "converges weakly in $L^2(0,T;H^{-1}(\Omega))$", so the statement is at least as strong as the page's. $C$ is the constant of Proposition 6.6: it is quantified before the basis, $f$, $g$ and the sequence.
-- source:
--   Hunter, Notes on Partial Differential Equations (revised 6/18/2014), p. 186, Proposition 6.7

import Mathlib
import Definitions.Def_HunterPDE_Parabolic_H10
import Definitions.Def_HunterPDE_Parabolic_WeakTimeDeriv
import Definitions.Def_HunterPDE_Parabolic_WeakSolution

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace HunterPDE.Parabolic

/-- Proposition 6.7 of Hunter, *Notes on PDEs* (revised 6/18/2014), p. 186: under Assumption 6.1,
a subsequence `u_{N_k}` of the approximate solutions (Definition 6.4) converges weakly to a weak
solution `u ∈ C([0, T]; L²(Ω)) ∩ L²(0, T; H¹₀(Ω))` of (6.8) (Definition 6.2) with
`u_t ∈ L²(0, T; H⁻¹(Ω))`, and there is a constant `C` with
`‖u‖_{L^∞(0,T;L²)} + ‖u‖_{L²(0,T;H¹₀)} + ‖u_t‖_{L²(0,T;H⁻¹)} ≤ C (‖f‖_{L²(0,T;H⁻¹)} + ‖g‖_{L²})`.

Weak convergence is stated in the concrete form of p. 186 and with the two convergences the
proof establishes: `u_{N_k} ⇀ u` in `L²(0, T; H¹₀)`, i.e. `∫₀ᵀ ⟨F, u_{N_k}⟩ dt → ∫₀ᵀ ⟨F, u⟩ dt` for
every `F ∈ L²(0, T; H⁻¹)`, and `u_{N_k t} ⇀ u_t` in `L²(0, T; H⁻¹)`, i.e.
`∫₀ᵀ ⟨u_{N_k t}, v⟩ dt → ∫₀ᵀ ⟨u_t, v⟩ dt` for every `v ∈ L²(0, T; H¹₀)`. The first implies the
printed "`u_{N_k}` converges weakly in `L²(0, T; H⁻¹)`". `C` is the constant of Proposition 6.6:
it is quantified before the basis, `f`, `g` and the approximate solutions. -/
theorem galerkin_limit {n : ℕ} (Ω : Set (EuclideanSpace ℝ (Fin n))) (hΩo : IsOpen Ω)
    (hΩb : Bornology.IsBounded Ω) (T : ℝ) (hT : 0 < T) (P : Coeffs n)
    (hP : P.Assumption61 Ω T) :
    ∃ C : ℝ≥0, ∀ (w : ℕ → H10 n Ω) (eig : ℕ → ℝ), IsDirichletEigenbasis Ω w eig →
      ∀ f : ℝ → Hm1 n Ω, MemLp f 2 (timeMeasure T) →
      ∀ (g : Lp ℝ 2 (volume.restrict Ω)) (uN uNt : ℕ → ℝ → H10 n Ω),
        (∀ N, IsApproxSolution Ω T P w N f g (uN N) (uNt N)) →
        ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ (u : ℝ → H10 n Ω) (ut : ℝ → Hm1 n Ω),
          IsWeakSolution Ω T P f g u ut ∧
          (∀ F : ℝ → Hm1 n Ω, MemLp F 2 (timeMeasure T) →
            Tendsto (fun k => ∫ t in Set.Ioo 0 T, F t (uN (φ k) t)) atTop
              (𝓝 (∫ t in Set.Ioo 0 T, F t (u t)))) ∧
          (∀ v : ℝ → H10 n Ω, MemLp v 2 (timeMeasure T) →
            Tendsto (fun k => ∫ t in Set.Ioo 0 T, l2Embed n Ω (uNt (φ k) t) (v t)) atTop
              (𝓝 (∫ t in Set.Ioo 0 T, ut t (v t)))) ∧
          eLpNorm (fun t => toL2 (u t)) ∞ (timeMeasure T) + eLpNorm u 2 (timeMeasure T) +
              eLpNorm ut 2 (timeMeasure T) ≤
            (C : ℝ≥0∞) * (eLpNorm f 2 (timeMeasure T) + ‖g‖ₑ) := by sorry

end HunterPDE.Parabolic
