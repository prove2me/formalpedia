-- Prove2me | Theorems.Thm_Monod_secondDerived_eq_bot_or_exists_free_abelian
-- name    : Monod.secondDerived_eq_bot_or_exists_free_abelian
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-30T13:08:31.92776+00:00
-- url     : https://prove2.me/theorems/724c26ae-9d5d-492b-98c1-b4e4eb8281e4
-- title:
--   Theorem 14 — ⟨f, g⟩ is metabelian or contains ℤ²
-- statement:
--   For $f, g \in H$, either the second derived subgroup of $\langle f, g\rangle$ is trivial ($\langle f, g\rangle$ is metabelian), or there is an injective homomorphism $\mathbf{Z}^2 \to \langle f, g\rangle$.
-- source:
--   Monod, N., Groups of piecewise projective homeomorphisms, Proc. Natl. Acad. Sci. USA 110 (2013) 4524–4527, https://doi.org/10.1073/pnas.1218426110 (arXiv:1209.5229v2, whose page numbers are used), p. 3, Theorem 14

import Mathlib
import Definitions.Def_Monod_PiecewiseProjective

namespace Monod

theorem secondDerived_eq_bot_or_exists_free_abelian {f g : OnePoint ℝ ≃ₜ OnePoint ℝ}
    (hf : f ∈ Hpp) (hg : g ∈ Hpp) :
    ⁅⁅Subgroup.closure {f, g}, Subgroup.closure {f, g}⁆,
        ⁅Subgroup.closure {f, g}, Subgroup.closure {f, g}⁆⁆ = ⊥ ∨
      ∃ φ : Multiplicative (ℤ × ℤ) →* (OnePoint ℝ ≃ₜ OnePoint ℝ),
        Function.Injective φ ∧ φ.range ≤ Subgroup.closure {f, g} := by
  sorry

end Monod
