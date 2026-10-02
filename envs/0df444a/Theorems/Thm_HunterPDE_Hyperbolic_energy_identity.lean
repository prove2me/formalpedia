-- Prove2me | Theorems.Thm_HunterPDE_Hyperbolic_energy_identity
-- name    : HunterPDE.Hyperbolic.energy_identity
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T00:51:36.366585+00:00
-- url     : https://prove2.me/theorems/a5f8d560-23c0-46ee-ad4e-084842566125
-- title:
--   Lemma 7.10 — energy identity (7.19) and absolute continuity of the energy (7.16)
-- statement:
--   Suppose $L$ is given by (7.4) and $a$ by (7.6), with coefficients satisfying Assumption 7.1. If
--   $u \in L^2(0,T;H^1_0(\Omega))$, $u_t \in L^2(0,T;L^2(\Omega))$, $u_{tt} \in L^2(0,T;H^{-1}(\Omega))$ and $u_{tt} + Lu \in L^2(0,T;L^2(\Omega))$ (7.18), then
--   $$\frac12\frac{d}{dt}\Big(\|u_t\|_{L^2}^2 + a(u,u;t)\Big) = (u_{tt} + Lu, u_t)_{L^2} + \frac12 a_t(u,u;t) \qquad (7.19)$$
--   and the energy $E = \|u_t\|^2_{L^2} + a(u,u;t)$ of (7.16) is an absolutely continuous function on $(0,T)$.
--
--   The identity is what makes the energy continuous in time for solutions that are too rough to be differentiated directly, and it is the step from weak to strong continuity of weak solutions.
--
--   **Formalization Note.** (7.18) is encoded by a function $F \in L^2(0,T;L^2(\Omega))$ with $\langle u_{tt}(t), v\rangle + a(u(t),v;t) = (F(t),v)_{L^2}$ for all $v \in H^1_0(\Omega)$, for a.e. $t$. The conclusion is: $2(F,u_t)_{L^2} + a_t(u,u;t)$ is integrable on $(0,T)$ and, for a constant $E_0$, $E(t) = E_0 + \int_0^t \big(2(F,u_t)_{L^2} + a_t(u,u;s)\big)\,ds$ for a.e. $t \in (0,T)$; this is (7.19) in integrated form, and says that $E$ (defined a.e., since $u_t$ is an $L^2$ class) is a.e. equal to an absolutely continuous function. The page prints (7.16) as $\|u_t\|_{L^2} + a(u,u;t)$ without the square; (7.19) and the proof of Proposition 7.11 use the square, which is taken here.
-- source:
--   Hunter, Notes on Partial Differential Equations (revised 6/18/2014), p. 218, Lemma 7.10, Eqs. (7.16), (7.18), (7.19)

import Mathlib
import Definitions.Def_HunterPDE_Hyperbolic_H10
import Definitions.Def_HunterPDE_Hyperbolic_WeakTimeDeriv
import Definitions.Def_HunterPDE_Hyperbolic_WaveOperator

namespace HunterPDE.Hyperbolic

open MeasureTheory Set

/-- Lemma 7.10 (Hunter, p. 218). Under Assumption 7.1, let `u ∈ L²(0, T; H¹₀(Ω))` with weak time
derivatives `u_t ∈ L²(0, T; L²(Ω))` and `u_tt ∈ L²(0, T; H⁻¹(Ω))`, and suppose (7.18):
`u_tt + L u = F ∈ L²(0, T; L²(Ω))`, i.e. `⟨u_tt(t), v⟩ + a(u(t), v; t) = (F(t), v)_{L²}` for all
`v ∈ H¹₀(Ω)`, for a.e. `t`. Then the right-hand side of (7.19),
`2 (u_tt + L u, u_t)_{L²} + a_t(u, u; t)`, is integrable on `(0, T)` and the energy
`E(t) = ‖u_t‖²_{L²} + a(u, u; t)` of (7.16) coincides a.e. on `(0, T)` with
`E₀ + ∫₀ᵗ (2 (u_tt + L u, u_t)_{L²} + a_t(u, u; s)) ds` for a constant `E₀`: that is, (7.19)
`(1/2) d/dt (‖u_t‖²_{L²} + a(u, u; t)) = (u_tt + L u, u_t)_{L²} + (1/2) a_t(u, u; t)` holds and
`E` is (a.e. equal to) an absolutely continuous function. -/
theorem energy_identity {n : ℕ} (Ω : Set (EuclideanSpace ℝ (Fin n))) (T : ℝ) (P : Coeffs n)
    (hA : Assumption71 Ω T P)
    (u : ℝ → H10 n Ω) (u_t : ℝ → L2 n Ω) (u_tt : ℝ → Hm1 n Ω)
    (hu : MemLp u 2 (volume.restrict (Ioo 0 T)))
    (hut : MemLp u_t 2 (volume.restrict (Ioo 0 T)))
    (hutt : MemLp u_tt 2 (volume.restrict (Ioo 0 T)))
    (hd1 : HasWeakTimeDeriv T (fun t => toL2 n Ω (u t)) u_t)
    (hd2 : HasWeakTimeDeriv T (fun t => l2ToHm1 (u_t t)) u_tt)
    (F : ℝ → L2 n Ω) (hF : MemLp F 2 (volume.restrict (Ioo 0 T)))
    (h718 : ∀ᵐ t ∂(volume.restrict (Ioo 0 T)), ∀ v : H10 n Ω,
      u_tt t v + form P (u t) v t = inner ℝ (F t) (toL2 n Ω v)) :
    IntegrableOn (fun t => 2 * inner ℝ (F t) (u_t t) + form_t P (u t) (u t) t) (Ioo 0 T) ∧
      ∃ E₀ : ℝ, ∀ᵐ t ∂(volume.restrict (Ioo 0 T)),
        ‖u_t t‖ ^ 2 + form P (u t) (u t) t =
          E₀ + ∫ s in (0 : ℝ)..t, (2 * inner ℝ (F s) (u_t s) + form_t P (u s) (u s) s) := by sorry

end HunterPDE.Hyperbolic
