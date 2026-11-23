-- Prove2me | Theorems.Thm_NoHair_static_conformal_adm_flux_law
-- name    : NoHair.static_conformal_adm_flux_law
-- status  : Proved
-- author  : @Igor Valuev
-- created : 2026-11-23T07:37:53.134161+00:00
-- url     : https://prove2.me/theorems/6df5904e-79f7-4d47-9c4a-e79247a1bc09
-- title:
--   ADM flux transformation on the positive conformal end
-- statement:
--   On a Cartesian asymptotically flat three-dimensional end suppose $N-1$ and $h-\delta$ are $O(r^{-1})$, with first derivatives $O(r^{-2})$. For $h_+=((1+N)/2)^4h$, the finite-radius ADM flux obeys
--   $$m_R(h_+)-m_R(h)+\frac1{4\pi}\int_{S_R}\partial_{\nu_\delta}N\,dA_\delta\longrightarrow 0.$$
--   This law permits arbitrary angular dependence. In particular, equality of ADM mass and limiting lapse flux forces zero ADM mass for the rescaled end.
-- source:
--   P. T. Chruściel, The classification of static vacuum space-times containing an asymptotically flat spacelike hypersurface with compact interior, Class. Quantum Grav. 16 (1999) 661–687, section 2, equations (2.1)–(2.4), and proof of Theorem 1.1 in section 5, equations (5.4)–(5.6), https://homepage.univie.ac.at/piotr.chrusciel/papers/chrusciel/static.pdf. G. L. Bunting and A. K. M. Masood-ul-Alam, Nonexistence of Multiple Black Holes in Asymptotically Euclidean Static Vacuum Space-Time, Gen. Relativ. Gravit. 19 (1987) 147–154, https://doi.org/10.1007/BF00770326. In the proof of Theorem 1.1, pp. 23–24 of the preprint, the rescaled end has zero mass by the ADM–Komar identity. R. Beig, Arnowitt–Deser–Misner energy and g00, Phys. Lett. A 69 (1978) 153–155, https://doi.org/10.1016/0375-9601(78)90198-6.

import Definitions.Def_NoHair_staticSliceADM

open NoHair Filter Set
open scoped Topology ContDiff Manifold

theorem NoHair.static_conformal_adm_flux_law (N : ADMPoint → ℝ) (h : ADMPoint → Matrix (Fin 3) (Fin 3) ℝ)
    (hdec : HasStaticFirstOrderFalloff N h) :
    Tendsto (fun r : ℝ => staticADMFlux (staticPositiveMetric N h) r - staticADMFlux h r
      + staticLapseFlux N r) atTop (𝓝 0) := by sorry
