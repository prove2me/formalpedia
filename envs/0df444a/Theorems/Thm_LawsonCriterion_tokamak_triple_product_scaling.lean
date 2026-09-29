-- Prove2me | Theorems.Thm_LawsonCriterion_tokamak_triple_product_scaling
-- name    : LawsonCriterion.tokamak_triple_product_scaling
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-21T11:21:18.893129+00:00
-- url     : https://prove2.me/theorems/1fbe204f-0035-47b2-b89b-eb36b9c1cf0a
-- title:
--   Tokamak scaling: the triple product is density-independent and scales as $T^{-1/3}$
-- statement:
--   A motivation specific to tokamaks for using the triple product rather than $n\tau_E$. Empirically the energy confinement time is found to be nearly proportional to $n^{1/3}/P^{2/3}$, and in an ignited plasma near the optimum temperature the heating power equals the fusion power and is therefore proportional to $n^2T^2$. Writing these as exact relations $\tau_E = c\,n^{1/3}/P^{2/3}$ and $P = a\,n^2T^2$ with positive $a$ and positive $n$, $T$, the density cancels identically and
--
--   $$n\,T\,\tau_E \;=\; c\,a^{-2/3}\,T^{-1/3}.$$
--
--   So the triple product does not depend on the density at all and depends on the temperature only through the weak factor $T^{-1/3}$, which is what makes it an adequate measure of the quality of a confinement scheme.
-- source:
--   Lawson criterion, Wikipedia, revision 1367242125, https://en.wikipedia.org/w/index.php?title=Lawson_criterion&oldid=1367242125 - section "Extension into the triple product", the empirical scaling τ_E ∝ n^{1/3} / P^{2/3} with P ∝ n²T², giving nTτ_E ∝ T^{-1/3}; after J. D. Lawson, Proc. Phys. Soc. B 70 (1957) 6-10, doi:10.1088/0370-1301/70/1/303

import Mathlib
import Definitions.Def_LawsonDTPlasma

namespace LawsonCriterion

/-- **Milestone.** The empirical tokamak scaling: if the energy confinement
time obeys `τ_E = c n^{1/3} / P^{2/3}` and, in an ignited plasma, the heating
power density is `P = a n² T²`, then the triple product `n T τ_E` is
independent of the density and scales as `T^{-1/3}`.
-/
theorem tokamak_triple_product_scaling (c a n T P tauE : ℝ)
    (hn : 0 < n) (hT : 0 < T) (ha : 0 < a)
    (hP : P = a * n ^ 2 * T ^ 2)
    (htau : tauE = c * n ^ ((1:ℝ) / 3) / P ^ ((2:ℝ) / 3)) :
    n * T * tauE = c * a ^ (-(2/3) : ℝ) * T ^ (-(1/3) : ℝ) := by sorry

end LawsonCriterion
