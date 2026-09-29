-- Prove2me | Theorems.Thm_GiuntiStudenikin2015_majorana_form_factor_constraints
-- name    : GiuntiStudenikin2015.majorana_form_factor_constraints
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-24T14:34:14.932681+00:00
-- url     : https://prove2.me/theorems/940ed9ba-276a-4d43-a0d6-080f71297a53
-- title:
--   Majorana form-factor matrices: imaginary antisymmetric or real symmetric
-- statement:
--   Let $\mathbb f$ be a Hermitian $N\times N$ complex matrix, $\mathbb f=\mathbb f^\dagger$ (3.66).
--
--   1. If $\mathbb f$ is antisymmetric, $\mathbb f=-\mathbb f^T$ (as the Majorana charge, magnetic and electric form-factor matrices are, (3.67)), then all its diagonal entries vanish, $\mathbb f_{ii}=0$, and it is purely imaginary:
--   $$\mathbb f=-\mathbb f^{*}.$$
--   2. If $\mathbb f$ is symmetric, $\mathbb f=\mathbb f^T$ (as the Majorana anapole form-factor matrix is, (3.68)), then it is real:
--   $$\mathbb f=\mathbb f^{*}.$$
--   Here $^{*}$ denotes entrywise complex conjugation.
--
--   Consequently a Majorana neutrino has no diagonal charge, magnetic or electric dipole form factors; only the anapole form factor can be diagonal.
-- source:
--   C. Giunti and A. Studenikin, *Neutrino electromagnetic interactions: A window to new physics*, Rev. Mod. Phys. 87, 531 (2015), https://doi.org/10.1103/RevModPhys.87.531, pp. 545–546, Sec. III.B, Eqs. (3.66)–(3.70)

import Mathlib
import Definitions.Def_GiuntiStudenikin2015_oscillation

namespace GiuntiStudenikin2015
theorem majorana_form_factor_constraints {N : ℕ} (f : Matrix (Fin N) (Fin N) ℂ)
    (hf : f.IsHermitian) :
    (f.transpose = -f → (∀ i, f i i = 0) ∧ f.map star = -f) ∧
    (f.transpose = f → f.map star = f) := by sorry
end GiuntiStudenikin2015
