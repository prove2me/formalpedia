-- Prove2me | Theorems.Thm_NewMinimalStandardModel_exists_massless_neutrino
-- name    : NewMinimalStandardModel.exists_massless_neutrino
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-04T15:31:59.851314+00:00
-- url     : https://prove2.me/theorems/f6832cf0-8fc0-4276-a1b9-dabbfb911d64
-- title:
--   New Minimal Standard Model: one neutrino is exactly massless
-- statement:
--   Let $v\in\mathbb R$ (with $\langle H\rangle = v/\sqrt2$), let $h_\nu$ be a complex $2\times 3$ Yukawa matrix, and let $M_1,M_2>0$ be the masses of the two right-handed neutrinos of Eq. (4). Let
--   $$\mathcal M = \begin{pmatrix} 0 & m_D^{\mathsf T} \\ m_D & \operatorname{diag}(M_1,M_2)\end{pmatrix},\qquad m_D=\frac{v}{\sqrt2}h_\nu,$$
--   be the $5\times5$ Majorana mass matrix of $(\nu_1,\nu_2,\nu_3,N_1,N_2)$. Then one of its physical masses vanishes exactly:
--   $$\exists\, i:\quad \sigma_i(\mathcal M) = \sqrt{\lambda_i(\mathcal M^\dagger\mathcal M)} = 0 .$$
--
--   This is the NMSM prediction that, with only two right-handed neutrinos, "one of the neutrino masses exactly vanishes (ignoring tiny Planck suppressed effects)" (p. 122), so that a neutrinoless double-beta-decay signal in near-future experiments is possible only for the inverted hierarchy.
--
--   **Formalization Note** The statement concerns the full tree-level neutral-lepton mass matrix, not the seesaw approximation; positivity of $M_1,M_2$ is the source's convention for the diagonal real basis.
-- source:
--   H. Davoudiasl, R. Kitano, T. Li, H. Murayama, The new Minimal Standard Model, Phys. Lett. B 609 (2005) 117-123, https://doi.org/10.1016/j.physletb.2005.01.026, p. 119 (Eq. (4) and the following discussion) and p. 122 ("one of the neutrino masses exactly vanishes")

import Mathlib
import Definitions.Def_NewMinimalStandardModel_Defs

namespace NewMinimalStandardModel

theorem exists_massless_neutrino (v : ℝ) (hν : Matrix (Fin 2) (Fin 3) ℂ) (M : Fin 2 → ℝ)
    (hM : ∀ α, 0 < M α) :
    ∃ i, majoranaMasses (neutralLeptonMassMatrix v hν M) i = 0 := by sorry

end NewMinimalStandardModel
