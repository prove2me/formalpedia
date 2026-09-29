-- Prove2me | Theorems.Thm_ModPForms_exists_forall_res_mul_eq_of_exists_prime_dvd_mod_three_eq_two_of_isAlgClosed
-- name    : ModPForms.exists_forall_res_mul_eq_of_exists_prime_dvd_mod_three_eq_two_of_isAlgClosed
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:12.70306+00:00
-- url     : https://prove2.me/theorems/f38bf68e-fafa-5d2a-9673-3e174ca4d08c
-- title:
--   Multiplicativity of supersingular residues in characteristic 3
-- statement:
--   Let $N'$ be a nonzero natural number with $3 \nmid N'$ admitting a prime divisor $q$ with $q \equiv 2 \pmod 3$, and let $F$ be an algebraically closed field of characteristic $3$. Write $\mathrm{modPMod}\,N'\,k\,F$ for the $F$-span inside $F[[q]]$ of those power series $\sum_n a_n q^n$ with $a_n \in \mathbb{Z}$ for which some modular form of weight $k$ on $\Gamma_0(N')$ has $q$-expansion coefficients equal to the $a_n$; and let $\mathrm{ssPlaces3}\,F\,N'$ be the set of places $x$ of the field $\mathrm{modularFunctionFieldC}\,F\,N' = F(\,j,\,j_{N'}\,) \subseteq F((q))$ (places being proper valuation subrings containing $F$ whose ring is a principal ideal ring) with $\mathrm{ord}_x(\mathrm{jGeomGen}\,F\,N') > 0$. The assertion is that there is a family $c = (c_x)_x$, with $c_x$ a nonzero element of the residue field of $x$ for each such place $x$, such that for every $m \in \mathbb{N}$ and all power series $\psi \in \mathrm{modPMod}\,N'\,4\,F$ and $\varphi \in \mathrm{modPMod}\,N'\,(2m+2)\,F$ and every $x$,
--   $$\mathrm{res}_{m+2}(\psi\varphi)(x) = c_x \cdot \mathrm{res}_1(\psi)(x) \cdot \mathrm{res}_m(\varphi)(x).$$
--   Here $\mathrm{res}_m(\phi)(x)$ is: $0$ unless $\phi$, viewed in $F((q))$, can be written $G \cdot (\mathrm{thetaJ}\,F)^m$ with $G$ in the modular function field, in which case, for a chosen such $G$ and a chosen uniformiser $\pi_x$ at $x$, it is the residue at $x$ of $G\,\pi_x^{a}$ with $a$ the natural-number truncation of $\mathrm{aPole}\,m\,x = \lfloor 7m\,\mathrm{ord}_x(\mathrm{jGeomGen}\,F\,N')/6\rfloor + 1$, and $0$ when $G\,\pi_x^{a}$ fails to lie in the valuation ring of $x$.
--
--   This is the multiplicativity, up to a place-dependent unit, of the residue functionals attached to the supersingular points of the level-$N'$ modular curve in characteristic $3$, the unit arising because the normalising exponent $\mathrm{aPole}$ is not additive in the weight index. It is used in the descending-weight ladder argument, being cited by [`ModPForms.mem_modPMod_sub_two_of_ladder_mul_mem_modPMod_add_two_of_not_three_dvd_of_dvd_of_mod_three_eq_two_of_isAlgClosed`](thm.html#ModPForms.mem_modPMod_sub_two_of_ladder_mul_mem_modPMod_add_two_of_not_three_dvd_of_dvd_of_mod_three_eq_two_of_isAlgClosed); the hypotheses on $N'$ and $F$ enter through the determination of $\mathrm{ord}_x(j)$ as $3$ or $6$ at supersingular places.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModPForms_exists_forall_res_mul_eq_of_exists_prime_dvd_mod_three_eq_two_of_isAlgClosed.lean

import Definitions.Def_ModularCurve_SSCarrier3
import Definitions.Def_CuspForm_ModPForms

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ModPForms.exists_forall_res_mul_eq_of_exists_prime_dvd_mod_three_eq_two_of_isAlgClosed
    (N' : ℕ) [NeZero N'] (hpN' : ¬ 3 ∣ N') (hε : ∃ q : ℕ, q.Prime ∧ q ∣ N' ∧ q % 3 = 2)
    (F : Type) [Field F] [CharP F 3] [IsAlgClosed F] :
    ∃ c : (x : ModularCurve.ssPlaces3 F N') → x.1.ResidueField, (∀ x, c x ≠ 0) ∧
      ∀ (m : ℕ) (ψ φ : PowerSeries F), ψ ∈ modPMod N' 4 F → φ ∈ modPMod N' (2 * (m : ℤ) + 2) F →
        ∀ x : ModularCurve.ssPlaces3 F N',
          ModularCurve.SSCarrier3.res (m + 2) (ψ * φ) x =
            c x * ModularCurve.SSCarrier3.res 1 ψ x * ModularCurve.SSCarrier3.res m φ x := by sorry
