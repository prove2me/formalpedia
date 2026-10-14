-- Prove2me | Theorems.Thm_OAI_AlternatingNS_velocity_construction
-- name    : OAI.AlternatingNS.velocity_construction
-- status  : Proved
-- author  : @SamenHossain
-- created : 2026-10-12T01:19:46.383018+00:00
-- url     : https://prove2.me/theorems/597f40f0-f8de-46a9-b9b1-547ad1a0973f
-- title:
--   Core construction: a computable, rapidly vanishing, divergence-free velocity whose observed trajectory detects halting
-- statement:
--   There are a computable map $(M,w)\mapsto c_{M,w}$ to field programs, a compact set $K\subset\mathbb R^3$ and velocity fields $U_{M,w}$ such that for every well-formed finite deterministic Turing machine $M$ and valid input $w$:
--
--   - $c_{M,w}$ is a program for $U_{M,w}$: it computes rational approximations of all mixed derivatives at rational points to any requested precision $2^{-k}$, effective moduli of continuity on bounded regions, and integer bounds for all weighted derivative norms;
--   - $U_{M,w}$ is smooth on $[0,\infty)\times\mathbb R^3$, spatially supported in $K$, rapidly decaying with all derivatives, starts from rest and is divergence-free;
--   - for every trajectory $\gamma$ of $U_{M,w}$ starting at $(-1,0,0)$,
--   $$\big(\exists t\ge0:\ \gamma_1(t)>0\big)\iff M\text{ halts on }w.$$
--
--   This is the analytic and effective core of the construction; the force, the Navier–Stokes equation, uniqueness and global trajectories are obtained from it by general arguments (sibling statements).
--
--   **Formalization Note** Fields are functions $\mathbb R\to\mathbb R^3\to E$ (`Field`); only $t\ge0$ matters. `Smooth` is $C^\infty$ on $[0,\infty)\times\mathbb R^3$, `Rapid` bounds $(1+t+\|x\|)^J\|\partial_t^l\partial_x^\alpha F\|$ for all $J,l,\alpha$, `SupportedIn F K` means $\operatorname{supp}F(t,\cdot)\subseteq K$ for $t\ge0$, `residual ν U` is $\partial_tU+(U\cdot\nabla)U-\nu\Delta U$, and time derivatives are taken within $[0,\infty)$. All notions are those of the published definition `NavierStokesAlternating`.
-- source:
--   OpenAI, "Computation under Rapidly Vanishing Navier–Stokes Forcing" (September 27, 2026), https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Computation-under-Rapidly-Vanishing-Navier-Stokes-Forcing-September-27-2026/manuscript.pdf; goal theorem OAI.AlternatingNS.alternating of the mission "Computation under Rapidly Vanishing Navier–Stokes Forcing"; the construction of the velocity field (Construction and Effective sections of the manuscript)

import Mathlib
import Definitions.Def_NavierStokesAlternating

namespace OAI

open scoped BigOperators ENNReal Topology ContDiff

open MeasureTheory

namespace AlternatingNS

/-- **Core construction.** A computable compiler of velocity programs and a compact set `K`
such that, for every well-formed machine `M` and valid input `w`, the compiled velocity field
is smooth, supported in `K`, rapidly decaying, divergence-free, starts from rest, and the
trajectory of the observed particle `(-1,0,0)` enters `{x₁ > 0}` exactly when `M` halts on `w`. -/
theorem velocity_construction :
    ∃ (U : Machine × List ℕ → Velocity) (compileVelocity : Machine × List ℕ → FieldProgram)
      (K : Set Space),
      Computable compileVelocity ∧ IsCompact K ∧
      ∀ (M : Machine) (w : List ℕ), M.WellFormed → M.ValidInput w →
        ProgramFor (compileVelocity (M, w)) (U (M, w)) ∧
        Smooth (U (M, w)) ∧ SupportedIn (U (M, w)) K ∧ Rapid (U (M, w)) ∧
        (∀ x, U (M, w) 0 x = 0) ∧
        (∀ t, 0 ≤ t → ∀ x, div (U (M, w)) t x = 0) ∧
        ∀ γ : ℝ → Space, IsTrajectory (U (M, w)) observedParticle γ →
          ((∃ t : ℝ, 0 ≤ t ∧ 0 < γ t 0) ↔ M.Halts w) := by
  sorry

end AlternatingNS
end OAI
