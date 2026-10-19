-- Prove2me | Theorems.Thm_HuWang2023_meanDMIGM_strictMonoOn
-- name    : HuWang2023.meanDMIGM_strictMonoOn
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-13T00:42:59.852987+00:00
-- url     : https://prove2.me/theorems/9be83350-63eb-4fc3-9aad-8e6c4c8387ef
-- title:
--   Eq. (5): $\langle \mathrm{DM_{IGM}}(z)\rangle$ is strictly increasing in redshift
-- statement:
--   Let $A>0$, $\Omega_b>0$, $H_0>0$ and $\Omega_m\ge0$, and let $f_{\rm IGM}$ and $f_e$ be functions that are continuous and strictly positive on $[0,\infty)$. Then the mean intergalactic dispersion measure of Eq. (5),
--   $$\langle {\rm DM_{IGM}}(z)\rangle = \frac{A\Omega_b H_0^2}{H_0}\int_0^{z}\frac{f_{\rm IGM}(z')f_e(z')(1+z')}{\sqrt{\Omega_m(1+z')^3+1-\Omega_m}}\,dz',$$
--   is a strictly increasing function of $z$ on $[0,\infty)$.
--
--   Strict monotonicity means the dispersion measure–redshift relation can be inverted, which is what allows FRBs to serve as distance indicators and cosmological probes (Section 3.4).
-- source:
--   Jian-Ping Hu and Fa-Yin Wang, *Hubble Tension: The Evidence of New Physics*, Universe 2023, 9(2), 94, https://doi.org/10.3390/universe9020094, Section 3.4 Fast Radio Burst, p. 6, Eq. (5) and the following paragraph

import Mathlib
import Definitions.Def_HuWang2023_HubbleTension_Defs

namespace HuWang2023

theorem meanDMIGM_strictMonoOn (A Ωb H0 Ωm : ℝ) (fIGM fe : ℝ → ℝ)
    (hA : 0 < A) (hΩb : 0 < Ωb) (hH0 : 0 < H0) (hΩm0 : 0 ≤ Ωm)
    (hfIGM_cont : ContinuousOn fIGM (Set.Ici 0)) (hfe_cont : ContinuousOn fe (Set.Ici 0))
    (hfIGM_pos : ∀ z, 0 ≤ z → 0 < fIGM z) (hfe_pos : ∀ z, 0 ≤ z → 0 < fe z) :
    StrictMonoOn (meanDMIGM A Ωb H0 Ωm fIGM fe) (Set.Ici 0) := by sorry

end HuWang2023
