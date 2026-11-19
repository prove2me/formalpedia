-- Prove2me | Theorems.Thm_GRH_grh_critical_line_iff
-- name    : GRH.grh_critical_line_iff
-- status  : Open
-- author  : @LG
-- created : 2026-11-18T17:50:36.512885+00:00
-- url     : https://prove2.me/theorems/6079bb22-1b0f-4fd6-b467-4b227db03fca
-- title:
--   GRH: critical-line form $\iff$ zero-free half-plane $\mathrm{Re}(s) > 1/2$
-- statement:
--   Two formulations of the **generalized Riemann hypothesis** are equivalent:
--
--   1. **Critical-line form (primitive characters).** For every integer $q \ge 1$, every primitive Dirichlet character $\chi$ modulo $q$, and every complex $s$ with $0 < \operatorname{Re}(s) < 1$: if $L(s,\chi) = 0$, then $\operatorname{Re}(s) = 1/2$.
--   2. **Zero-free form (all characters).** For every integer $q \ge 1$, every Dirichlet character $\chi$ modulo $q$, and every complex $s$ with $\operatorname{Re}(s) > 1/2$, except the pair $(\chi, s) = (1, 1)$: $L(s,\chi) \ne 0$.
--
--   Form 1 is the classical statement of GRH as given for primitive characters; form 2 is the mission's goal (the campaign template at $\theta = 1/2$). This equivalence identifies the two, so the goal formalizes exactly the classical conjecture.
--
--   **Formalization Note.** Both sides quantify over positive moduli via `[NeZero q]`. `IsPrimitive` means that the conductor equals the modulus. `LFunction` is Mathlib's analytic continuation, defined at every complex $s$.
-- source:
--   https://en.wikipedia.org/wiki/Generalized_Riemann_hypothesis (sections 'Generalized Riemann hypothesis (GRH)' and 'Background': primitive characters, trivial zeros, functional equation and critical strip; oldid 1378052002); zero-free form: Prove2Me campaign 'Towards the Generalized Riemann Hypothesis' (https://prove2.me/campaigns/towards-grh), template at theta = 1/2.

import Mathlib

namespace GRH

theorem grh_critical_line_iff :
    (∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ.IsPrimitive →
      ∀ s : ℂ, 0 < s.re → s.re < 1 → DirichletCharacter.LFunction χ s = 0 → s.re = 1 / 2) ↔
    (∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (s : ℂ),
      (1 / 2 : ℝ) < s.re → ¬ (χ = 1 ∧ s = 1) → DirichletCharacter.LFunction χ s ≠ 0) := by
  sorry

end GRH
