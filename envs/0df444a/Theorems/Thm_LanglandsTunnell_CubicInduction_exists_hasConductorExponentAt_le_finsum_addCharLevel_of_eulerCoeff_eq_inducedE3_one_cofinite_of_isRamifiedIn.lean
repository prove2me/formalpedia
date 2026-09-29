-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_exists_hasConductorExponentAt_le_finsum_addCharLevel_of_eulerCoeff_eq_inducedE3_one_cofinite_of_isRamifiedIn
-- name    : LanglandsTunnell.CubicInduction.exists_hasConductorExponentAt_le_finsum_addCharLevel_of_eulerCoeff_eq_inducedE3_one_cofinite_of_isRamifiedIn
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:04.547556+00:00
-- url     : https://prove2.me/theorems/d0286160-fdf7-5657-a453-fb4041df30e5
-- title:
--   Conductor bound at ramified places, cofinite Euler data
-- statement:
--   Let $K$ be a number field equipped with an algebra structure of $\mathcal{O}_{\mathbb{Q}}$ on $\mathcal{O}_K$ making the latter integral over the former, and assume $[K:\mathbb{Q}]=3$. Let $\omega \colon (\mathbb{A}_{\mathbb{Q}})^{\times} \to \mathbb{C}^{\times}$ be a monoid homomorphism which is an admissible twist, i.e. trivial on the principal ideles $\iota(u)$ for $u \in \mathbb{Q}^{\times}$, continuous, and of absolute value $1$ at every idele. Let $S$ be a finite set of height-one primes of $\mathcal{O}_{\mathbb{Q}}$, and assume that for every prime $p \notin S$ that is not ramified in $K$ — ramification at $p$ meaning that some prime $\mathfrak{P}$ of $\mathcal{O}_K$ with $\mathfrak{P} \cap \mathcal{O}_{\mathbb{Q}} = p$ has $e(\mathfrak{P}/p) \neq 1$ — the local character $\omega_p$ is trivial on all units of $\mathbb{Q}_p$ whose inverse is again integral, and $\omega_p(\varpi_p)$, the Euler coefficient of $\omega$ at $p$, equals $\mathrm{inducedE3}$ of the coefficient function $\mathrm{inducedCoeff}\,K\,1$ at $p$, namely minus the coefficient of $X^3$ in the product of the local induced factors over the primes of $K$ above $p$ attached to the trivial idele class character of $K$. Let $v$ be a prime of $\mathcal{O}_{\mathbb{Q}}$ ramified in $K$. Then there is a natural number $t$ which is a conductor exponent for $\omega_v$, in the sense that $\omega_v$ is trivial on the $t$-th higher unit group at $v$ while for each $m<t$ some unit of the $m$-th higher unit group is not killed by $\omega_v$, and which satisfies $t \le \sum_{w \mid v} f(w/v)\cdot n_w$, where $f(w/v)$ is the inertia degree and $n_w$ is the level of the standard local additive character $\psi_w$ of $K_w$, i.e. the supremum of the integers $n$ such that $\psi_w$ is trivial on all elements of valuation at most $\exp(n)$.
--
--   This is the ramified-place half of the conductor estimate for the twisting character in the Langlands–Tunnell converse-theorem argument, in the case of trivial auxiliary character: the bound is by the sum $\sum_{w\mid v} f(w/v)\,n_w$, the local expression of the different (equivalently discriminant) exponent in the conductor–discriminant formalism. It is used by [`LanglandsTunnell.CubicInduction.exists_hasConductorExponentAt_le_finsum_pinnedExp_of_eulerCoeff_eq_inducedE3`](thm.html#LanglandsTunnell.CubicInduction.exists_hasConductorExponentAt_le_finsum_pinnedExp_of_eulerCoeff_eq_inducedE3), where it is combined with the unramified case and a factorisation of a general admissible twist.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_exists_hasConductorExponentAt_le_finsum_addCharLevel_of_eulerCoeff_eq_inducedE3_one_cofinite_of_isRamifiedIn.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_HeckeDatum
import Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import Definitions.Def_LanglandsTunnell_CubicLambda
import Definitions.Def_LanglandsTunnell_ConverseData

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField NumberField.TateGlobal AutomorphicForm LanglandsTunnell.Converse
  LanglandsTunnell.CubicInduction LanglandsTunnell.RankinSelberg LanglandsTunnell.CubicLambda
  LanglandsTunnell.TateLocal

theorem LanglandsTunnell.CubicInduction.exists_hasConductorExponentAt_le_finsum_addCharLevel_of_eulerCoeff_eq_inducedE3_one_cofinite_of_isRamifiedIn
    (K : Type) [Field K] [NumberField K]
    [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
    (_hdeg : Module.finrank ℚ K = 3)
    (ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (_hω : IsAdmissibleTwist ℚ ω)
    (S : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (_hωS : ∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ S → ¬ IsRamifiedIn K p →
      IsUnramifiedCharAt ω p ∧ eulerCoeff ℚ ω p = inducedE3 ℚ (inducedCoeff K 1) p)
    (v : HeightOneSpectrum (𝓞 ℚ)) (_hv : IsRamifiedIn K v) :
    ∃ t : ℕ, LanglandsTunnell.TateLocal.HasConductorExponentAt ℚ v (localChar ω v) t ∧
      (t : ℤ) ≤ ∑ᶠ w ∈ primeFibre ℚ K v,
        (v.asIdeal.inertiaDeg' w.asIdeal : ℤ) *
          LanglandsTunnell.TateLocal.addCharLevel (NumberField.StandardAddChar.psiLocal K w) := by sorry
