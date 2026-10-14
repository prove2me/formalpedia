-- Prove2me | Theorems.Thm_Giddings1999_normalizable_modes_classification
-- name    : Giddings1999.normalizable_modes_classification
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-13T01:53:00.782679+00:00
-- url     : https://prove2.me/theorems/1666de78-0e99-4872-a501-4d1410e32221
-- title:
--   Eqs. (3)–(7): normalizable modes of global $\mathrm{AdS}_{d+1}$ occur exactly at $|\omega|=2h_++2n+l$
-- statement:
--   Let $d\ge2$, $R>0$, $m\in\mathbb R$, $l\in\mathbb N$ and $\omega\in\mathbb R$, and let $\nu=\tfrac12\sqrt{d^2+4m^2R^2}$, $2h_+=\tfrac d2+\nu$. A radial profile $\chi$ is a normalizable mode of the free Klein–Gordon equation on global $\mathrm{AdS}_{d+1}$ with angular momentum $l$ and frequency $\omega$ (a nonzero solution of the radial equation that is regular at $r=0$ and has finite Klein–Gordon norm) if and only if there is $n\in\mathbb N$ with
--   $$|\omega|=\omega_{nl}=2h_++2n+l$$
--   and a constant $c\neq0$ such that $\chi=c\,\chi_{nl}$ on $(0,\pi/2)$, where $\chi_{nl}(r)=\sin^l r\,(\cos r)^{2h_+}P_n^{(l+d/2-1,\nu)}(\cos 2r)$.
--
--   This is the statement of eqs. (5)–(7) that free solutions exist at every frequency but are normalizable only on the discrete spectrum $\omega_{nl}$, and that the normalizable ones are the modes $\chi_{nl}$.
--
--   **Formalization Note** "Regular at the origin" means $|\chi|$ is bounded on $(0,\pi/4]$. "Finite Klein–Gordon norm" means $\tan^{d-1}r\,\chi(r)^2$ is integrable on $(0,\pi/2)$. The hypothesis $d\ge2$ gives $\nu\ge1$, so the $(\cos r)^{2h_-}$ branch is never normalizable.
-- source:
--   S. B. Giddings, Boundary S matrix and the anti-de Sitter space to conformal field theory dictionary, Phys. Rev. Lett. 83, 2707 (1999), https://doi.org/10.1103/PhysRevLett.83.2707, eqs. (3)–(7), p. 2707

import Mathlib
import Definitions.Def_Giddings1999_AdSModes

open Real Filter Topology

namespace Giddings1999

/-- **Goal** (eqs. 3–7): a radial profile `χ` is a normalizable mode of angular momentum `l` and
frequency `ω` iff `|ω| = ω_{nl} = 2h₊ + 2n + l` for some `n ∈ ℕ` and `χ` is a nonzero multiple of the
explicit mode `χ_{nl}` of eq. (5). -/
theorem normalizable_modes_classification (d : ℕ) (hd : 2 ≤ d) (m R : ℝ) (hR : 0 < R)
    (ω : ℝ) (l : ℕ) (χ : ℝ → ℝ) :
    IsNormalizableMode d m R ω l χ ↔
      ∃ n : ℕ, |ω| = omegaNL d m R n l ∧
        ∃ c : ℝ, c ≠ 0 ∧ Set.EqOn χ (fun r => c * modeRadial d m R n l r) (Set.Ioo 0 (π / 2)) := by
  sorry

end Giddings1999
