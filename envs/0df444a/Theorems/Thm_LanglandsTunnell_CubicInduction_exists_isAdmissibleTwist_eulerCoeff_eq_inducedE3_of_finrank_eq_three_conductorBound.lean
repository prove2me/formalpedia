-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_exists_isAdmissibleTwist_eulerCoeff_eq_inducedE3_of_finrank_eq_three_conductorBound
-- name    : LanglandsTunnell.CubicInduction.exists_isAdmissibleTwist_eulerCoeff_eq_inducedE3_of_finrank_eq_three_conductorBound
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:04.547556+00:00
-- url     : https://prove2.me/theorems/8ffd4d9a-484e-556e-8aaf-46c3dc0593e1
-- title:
--   Central character of cubic induction, with conductor bound
-- statement:
--   Let $K$ be a number field of degree $3$ over $\mathbb Q$, with $\mathcal O_K$ an integral $\mathcal O_{\mathbb Q}$-algebra, and let $\mu$ be a homomorphism from the ideles $(\mathbb A_K)^\times$ to $\mathbb C^\times$ which is admissible, i.e. trivial on the image of $K^\times$, continuous, and of absolute value $1$ everywhere. Then there is an admissible character $\omega$ of $(\mathbb A_{\mathbb Q})^\times$ with three properties. (i) For every prime $p$ of $\mathcal O_{\mathbb Q}$ which is not a bad place for $(K,\mu)$ — that is, no prime $\mathfrak P$ above $p$ has ramification index $\neq 1$ and the local component of $\mu$ at each such $\mathfrak P$ is trivial on the local units — the local component of $\omega$ at $p$ is trivial on the local units and $\mathrm{eulerCoeff}$ of $\omega$ at $p$, namely $\omega$ evaluated at a uniformiser idele, equals $-$ the coefficient of $X^3$ in the induced Euler polynomial at $p$ built from the coefficients $\mathrm{inducedCoeff}\,K\,\mu$ ($\mu$ at a uniformiser idele of $\mathfrak P$ when unramified there, $0$ otherwise) over the primes of the fibre above $p$. (ii) If, for data $u^{\mathrm R}_w\in\mathbb C$, $a_w\in\mathbb Z/2$ at the real places $w$ of $K$ and $u^{\mathbb C}_w\in\mathbb C$, $k_w\in\mathbb Z$ at the complex places, the archimedean component of $\mu$ at each real $w$ is $x\mapsto \|x\|^{m_w u^{\mathrm R}_w}(x/\|x\|)^{\tilde a_w}$ with $\tilde a_w$ the representative of $a_w$ in $\{0,1\}$, and at each complex $w$ is the corresponding expression with $(u^{\mathbb C}_w,k_w)$, then at the real place of $\mathbb Q$ the archimedean component of $\omega$ has parameters $\sum_{w\ \mathrm{real}}u^{\mathrm R}_w+\sum_{w\ \mathrm{cplx}}2u^{\mathbb C}_w$ and $\sum_{w\ \mathrm{real}}\tilde a_w+\sum_{w\ \mathrm{cplx}}(k_w+1)$ (unordered sums over the places). (iii) For every prime $p$ and every $M\in\mathbb N$: if each prime $\mathfrak P$ of $K$ above $p$ carries a conductor exponent $a_{\mathfrak P}\le M$ for the local component of $\mu$ at $\mathfrak P$ (trivial on the $a_{\mathfrak P}$-th higher unit group and nontrivial on each lower one), then the local component of $\omega$ at $p$ has a conductor exponent $e\le M+4$.
--
--   The character $\omega$ is the central character of the automorphic induction, from the cubic field $K$ to $\mathbb Q$, of the idele class character $\mu$: its Euler coefficients at good primes are prescribed by the degree-three term of the induced Euler polynomial, its archimedean parameters by the sums over the places of $K$, and its local conductor exponents are bounded in terms of those of $\mu$. It feeds the Rankin–Selberg statement on the analytic continuation of the $L$-function attached to the induced datum, where the conductor bound controls the level.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_exists_isAdmissibleTwist_eulerCoeff_eq_inducedE3_of_finrank_eq_three_conductorBound.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import Definitions.Def_LanglandsTunnell_CubicLambda

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField NumberField.TateGlobal LanglandsTunnell.Converse LanglandsTunnell.RankinSelberg
  LanglandsTunnell.CubicLambda

theorem LanglandsTunnell.CubicInduction.exists_isAdmissibleTwist_eulerCoeff_eq_inducedE3_of_finrank_eq_three_conductorBound
    (K : Type) [Field K] [NumberField K] [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
    (hdeg : Module.finrank ℚ K = 3)
    (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (hμ : IsAdmissibleTwist K μ) :
    ∃ ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ, IsAdmissibleTwist ℚ ω ∧
      (∀ p : HeightOneSpectrum (𝓞 ℚ), ¬ IsBadPlace K μ p →
        IsUnramifiedCharAt ω p ∧ eulerCoeff ℚ ω p = inducedE3 ℚ (inducedCoeff K μ) p) ∧
      (∀ (uR : ∀ w : InfinitePlace K, w.IsReal → ℂ) (aR : ∀ w : InfinitePlace K, w.IsReal → ZMod 2)
        (uC : ∀ w : InfinitePlace K, w.IsComplex → ℂ) (kC : ∀ w : InfinitePlace K, w.IsComplex → ℤ),
        (∀ w, ∀ hw : w.IsReal, IsArchCompAt K μ w (uR w hw) ((aR w hw).val : ℤ)) →
        (∀ w, ∀ hw : w.IsComplex, IsArchCompAt K μ w (uC w hw) (kC w hw)) →
        ∀ v : InfinitePlace ℚ, v.IsReal →
          IsArchCompAt ℚ ω v
            ((∑ᶠ (w) (hw : w.IsReal), uR w hw) + (∑ᶠ (w) (hw : w.IsComplex), 2 * uC w hw))
            ((∑ᶠ (w) (hw : w.IsReal), ((aR w hw).val : ℤ)) + (∑ᶠ (w) (hw : w.IsComplex), (kC w hw + 1)))) ∧

      ∀ (p : HeightOneSpectrum (𝓞 ℚ)) (M : ℕ),
        (∀ w ∈ primeFibre ℚ K p, ∃ aw : ℕ, aw ≤ M ∧
          LanglandsTunnell.TateLocal.HasConductorExponentAt K w (NumberField.TateGlobal.localChar μ w) aw) →
        ∃ e : ℕ, e ≤ M + 4 ∧
          LanglandsTunnell.TateLocal.HasConductorExponentAt ℚ p (NumberField.TateGlobal.localChar ω p) e := by sorry
