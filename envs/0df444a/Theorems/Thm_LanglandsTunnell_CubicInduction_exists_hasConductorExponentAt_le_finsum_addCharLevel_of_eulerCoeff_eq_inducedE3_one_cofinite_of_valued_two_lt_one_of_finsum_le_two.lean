-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_exists_hasConductorExponentAt_le_finsum_addCharLevel_of_eulerCoeff_eq_inducedE3_one_cofinite_of_valued_two_lt_one_of_finsum_le_two
-- name    : LanglandsTunnell.CubicInduction.exists_hasConductorExponentAt_le_finsum_addCharLevel_of_eulerCoeff_eq_inducedE3_one_cofinite_of_valued_two_lt_one_of_finsum_le_two
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:04.547556+00:00
-- url     : https://prove2.me/theorems/a9bb8ae7-7c73-592f-9761-37eae5dfe7ee
-- title:
--   Conductor bound for ωᵥ at a ramified dyadic place
-- statement:
--   Let $K$ be a number field whose ring of integers is an integral algebra over $\mathbb{Z} = \mathcal{O}_{\mathbb{Q}}$ and with $[K:\mathbb{Q}] = 3$. Let $\omega$ be a homomorphism from the ideles of $\mathbb{Q}$ to $\mathbb{C}^{\times}$ which is an admissible twist, i.e. trivial on the image of $\mathbb{Q}^{\times}$, continuous, and of absolute value $1$ at every idele. Let $S$ be a finite set of primes of $\mathbb{Z}$ and assume that for every prime $p \notin S$ that is unramified in $K$ (no prime of $\mathcal{O}_K$ over $p$ has ramification index $\neq 1$) the local character $\omega_p$ is trivial on the units of the valuation ring of $\mathbb{Q}_p$, and the Euler coefficient $\omega_p$ at a uniformizer idele equals $\mathrm{inducedE3}$ at $p$, that is minus the coefficient of $X^3$ in the induced Euler polynomial formed from the coefficients $\mathrm{inducedCoeff}\,K\,1$ of the trivial character of $K$. Let $v$ be a prime of $\mathbb{Z}$ that is ramified in $K$, with $|2|_v < 1$, and suppose $\sum_{w \mid v} f(w/v)\, n_w \le 2$, the sum being over the primes $w$ of $\mathcal{O}_K$ lying over $v$, where $f(w/v)$ is the inertia degree and $n_w$ is the level of the standard local additive character $\psi_w$ of $K_w$, the largest $n$ with $\psi_w$ trivial on $\{|x| \le q^{n}\}$. Then there is a natural number $t$ such that $\omega_v$ has conductor exponent $t$, i.e. $\omega_v$ is trivial on the $t$-th higher unit group at $v$ and nontrivial on the $m$-th for every $m < t$, and $t \le \sum_{w \mid v} f(w/v)\, n_w$.
--
--   This is the dyadic case of the bound, by the valuation of the discriminant of $K$, for the conductor exponent of the quadratic resolvent character $\omega$ attached to a cubic field, the sum $\sum_{w\mid v} f(w/v)\, n_w$ being the $v$-adic valuation of $\operatorname{disc} K$. It supplies the one place left open by the general conductor estimate [`LanglandsTunnell.CubicInduction.exists_hasConductorExponentAt_le_finsum_addCharLevel_of_eulerCoeff_eq_inducedE3_one_cofinite_of_isRamifiedIn`](thm.html#LanglandsTunnell.CubicInduction.exists_hasConductorExponentAt_le_finsum_addCharLevel_of_eulerCoeff_eq_inducedE3_one_cofinite_of_isRamifiedIn), which is where level bounds for the twist $\omega$ used in the Langlands–Tunnell argument come from.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_exists_hasConductorExponentAt_le_finsum_addCharLevel_of_eulerCoeff_eq_inducedE3_one_cofinite_of_valued_two_lt_one_of_finsum_le_two.lean

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

theorem LanglandsTunnell.CubicInduction.exists_hasConductorExponentAt_le_finsum_addCharLevel_of_eulerCoeff_eq_inducedE3_one_cofinite_of_valued_two_lt_one_of_finsum_le_two
    (K : Type) [Field K] [NumberField K]
    [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
    (hdeg : Module.finrank ℚ K = 3)
    (ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (hω : IsAdmissibleTwist ℚ ω)
    (S : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (hωS : ∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ S → ¬ IsRamifiedIn K p →
      IsUnramifiedCharAt ω p ∧ eulerCoeff ℚ ω p = inducedE3 ℚ (inducedCoeff K 1) p)
    (v : HeightOneSpectrum (𝓞 ℚ)) (hv : IsRamifiedIn K v)
    (h2 : Valued.v (2 : v.adicCompletion ℚ) < 1)
    (hle : ∑ᶠ w ∈ primeFibre ℚ K v,
        (v.asIdeal.inertiaDeg' w.asIdeal : ℤ) *
          LanglandsTunnell.TateLocal.addCharLevel (NumberField.StandardAddChar.psiLocal K w) ≤ 2) :
    ∃ t : ℕ, LanglandsTunnell.TateLocal.HasConductorExponentAt ℚ v (localChar ω v) t ∧
      (t : ℤ) ≤ ∑ᶠ w ∈ primeFibre ℚ K v,
        (v.asIdeal.inertiaDeg' w.asIdeal : ℤ) *
          LanglandsTunnell.TateLocal.addCharLevel (NumberField.StandardAddChar.psiLocal K w) := by sorry
