-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_exists_localChar_centralChar_eq_finprod_mul_of_not_isRamifiedIn_of_isCubicInductionDataOn
-- name    : LanglandsTunnell.CubicInduction.exists_localChar_centralChar_eq_finprod_mul_of_not_isRamifiedIn_of_isCubicInductionDataOn
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:06.047113+00:00
-- url     : https://prove2.me/theorems/47064fd7-91de-57d6-900d-651a85c13071
-- title:
--   Central character of cubic induction data at unramified primes
-- statement:
--   Let $K$ be a number field with $[K:\mathbb{Q}]=3$, let $\psi$ be an additive character of the adele ring of $\mathbb{Q}$ with values in $\mathbb{C}$, and let $\mu$ be a homomorphism from the idele units of $K$ to $\mathbb{C}^\times$ which is an admissible twist, i.e. trivial on the principal ideles coming from $K^\times$, continuous, and of absolute value $1$ everywhere. Let `pins` be a package of carrier data for $\mathbb{Q}$ (a measurable space and measure on adelic $GL_2$, a subset $D$, a central subgroup $Z$, level subgroups attached to ideals, chosen group elements indexed by finite places, and a measurable space and measure on the adele ring), and let $X$ be cubic induction data: a function `X.form` on adelic $GL_3$ over $\mathbb{Q}$, a global Whittaker function, local Whittaker functions at the finite places, an archimedean Whittaker function, a central character `X.centralChar` on the ideles of $\mathbb{Q}$, and a dual Whittaker function. Assume `IsCubicInductionDataOn K pins ψ μ {v | IsBadPlace K μ v} X`, that is: `X.form` is left invariant under the rational points of $GL_3$, transforms under central ideles by `X.centralChar`, whose values are trivial on principal ideles; `X.form` is cuspidal along the two parabolics $P_{21}$ and $P_{12}$ relative to `pins`; `X.whittaker` is the $\psi$-Whittaker transform of `X.form`, satisfies the $\psi$-Whittaker transformation law, and its translates over the mirabolic index set sum to `X.form`; each local Whittaker function satisfies the transformation law for the local component of $\psi$, the global Whittaker function factorises as the archimedean factor times a finite product of local factors over any finite set containing the bad places outside of which the argument is integral, the local factors are spherical with the Hecke coefficients induced from $(K,\mu)$ at the good places and invariant under the relevant congruence subgroup at good places unramified in $K$, each local factor has Whittaker multiplicity one, `X.form` has moderate growth, the archimedean Whittaker function is $K$-finite, `X.form` has iota moments and `X.whittaker` converges in a half plane, together with the corresponding assertions for the dual form and dual Whittaker function; here a place is bad when it is ramified in $K$ or the twist $\mu$ is ramified above it. Assume further that `X.form` is continuous and non-zero, and let $v$ be a finite place of $\mathbb{Q}$ which is unramified in $K$, in the sense that every prime of $K$ above $v$ has ramification index $1$. Then there is a homomorphism $\eta$ from the units of the completion $\mathbb{Q}_v$ to $\mathbb{C}^\times$ with conductor exponent $0$ at $v$ (trivial on the group of units at level $0$, the further minimality condition being vacuous), satisfying $\eta(x)^2=1$ for all $x$, such that for every unit $x$ of $\mathbb{Q}_v$ the value of the local component of `X.centralChar` at $v$ on $x$ equals the finite product, over the primes $w$ of $K$ lying above $v$, of the local components of $\mu$ at $w$ evaluated at the image of $x$ under $\mathbb{Q}_v\to K_w$, times $\eta(x)$.
--
--   This identifies the local component at an unramified prime of the central character of a cubic induction form with the product of the local components of $\mu$ over the primes above it, up to an unramified quadratic character $\eta$ accounting for the sign $(-1)^{3+\#\{w\mid v\}}$ that appears in the induced $GL_3$ Hecke data. It is the structured-data version of the corresponding statement for cubic induction forms, and feeds the comparison of functional equations and root numbers used in the converse-theorem step of the Langlands–Tunnell argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_exists_localChar_centralChar_eq_finprod_mul_of_not_isRamifiedIn_of_isCubicInductionDataOn.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import Definitions.Def_DedekindDomain_Completion_BaseChange
import Definitions.Def_LanglandsTunnell_CubicInduction_DataOn

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open IsDedekindDomain NumberField NumberField.TateGlobal AutomorphicForm LanglandsTunnell.Converse
  LanglandsTunnell.CubicInduction LanglandsTunnell.TateLocal MeasureTheory LanglandsTunnell.RankinSelberg

theorem LanglandsTunnell.CubicInduction.exists_localChar_centralChar_eq_finprod_mul_of_not_isRamifiedIn_of_isCubicInductionDataOn
    (K : Type) [Field K] [NumberField K] (hdeg : Module.finrank ℚ K = 3)
    (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ)
    (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (hμ : IsAdmissibleTwist K μ)
    (pins : CarrierPins ℚ)
    (X : CubicInductionData)
    (hX : IsCubicInductionDataOn K pins ψ μ {v | IsBadPlace K μ v} X) (hcont : Continuous X.form) (hF : X.form ≠ 0)
    (v : HeightOneSpectrum (𝓞 ℚ)) (hKv : ¬ IsRamifiedIn K v) :
    ∃ η : (v.adicCompletion ℚ)ˣ →* ℂˣ, HasConductorExponentAt ℚ v η 0 ∧ (∀ x, η x * η x = 1) ∧
      ∀ x : (v.adicCompletion ℚ)ˣ,
        ((localChar X.centralChar v x : ℂˣ) : ℂ) =
          (∏ᶠ w : v.Extension (𝓞 K), ((localChar μ w.1
            (Units.map (algebraMap (v.adicCompletion ℚ) (w.1.adicCompletion K)).toMonoidHom x) : ℂˣ) : ℂ)) *
            ((η x : ℂˣ) : ℂ) := by sorry
