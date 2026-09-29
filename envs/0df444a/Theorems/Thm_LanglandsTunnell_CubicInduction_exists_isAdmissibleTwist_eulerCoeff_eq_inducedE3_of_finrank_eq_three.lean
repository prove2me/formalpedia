-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_exists_isAdmissibleTwist_eulerCoeff_eq_inducedE3_of_finrank_eq_three
-- name    : LanglandsTunnell.CubicInduction.exists_isAdmissibleTwist_eulerCoeff_eq_inducedE3_of_finrank_eq_three
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:04.547556+00:00
-- url     : https://prove2.me/theorems/8255e5f0-35b3-5208-a300-e3f183ccc959
-- title:
--   Admissible character induced from a cubic field
-- statement:
--   Let $K$ be a number field with $[K:\mathbb{Q}]=3$, equipped with an $\mathcal{O}_{\mathbb{Q}}$-algebra structure on $\mathcal{O}_K$ making $\mathcal{O}_K$ integral over $\mathcal{O}_{\mathbb{Q}}$, and let $\mu$ be a homomorphism from the ideles $(\mathbb{A}_K)^\times$ to $\mathbb{C}^\times$ which is an admissible twist, i.e. trivial on the principal ideles coming from $K^\times$, continuous, and of absolute value $1$ everywhere. Then there is a homomorphism $\omega : (\mathbb{A}_{\mathbb{Q}})^\times \to \mathbb{C}^\times$, again trivial on principal ideles, continuous and unitary, with the following two properties. First, for every finite place $p$ of $\mathbb{Q}$ that is not a bad place for $(K,\mu)$ — that is, every prime of $\mathcal{O}_K$ in the fibre over $p$ has ramification index $1$ over $p$, and the local character of $\mu$ is trivial on the units of the completion at each such prime — the local character of $\omega$ at $p$ is trivial on the units of $\mathbb{Q}_p$ and its Euler coefficient $\omega(\pi_p)$, the value at a uniformizer idele, equals $\mathrm{inducedE3}$ of the coefficient system $\mathfrak{P}\mapsto \mu(\pi_{\mathfrak{P}})$ (set to $0$ at primes where $\mu$ ramifies) at $p$, namely minus the coefficient of $X^3$ in the induced Euler polynomial $\prod_{\mathfrak{P}\mid p} \mathrm{inducedFactor}$. Second, for any families $u_w\in\mathbb{C}$, $a_w\in\mathbb{Z}/2$ indexed by the real places of $K$ and $u'_w\in\mathbb{C}$, $k_w\in\mathbb{Z}$ indexed by the complex places, such that the archimedean component of $\mu$ at each real place $w$ is $x\mapsto \|x\|^{m_w u_w}(x/\|x\|)^{\tilde a_w}$ with $\tilde a_w$ the integer lift of $a_w$, and at each complex place $w$ is $x\mapsto \|x\|^{m_w u'_w}(x/\|x\|)^{k_w}$, the archimedean component of $\omega$ at every real place of $\mathbb{Q}$ has exponents $\sum_w u_w + \sum_w 2u'_w$ and $\sum_w \tilde a_w + \sum_w (k_w+1)$, the sums being finite sums over the real, respectively complex, places of $K$.
--
--   This produces the central character attached to the automorphic induction of an idele class character of a cubic field, specified by its Euler coefficients away from the ramification of $K$ and of $\mu$ and by its archimedean exponents. It is used in bounding the conductor exponents of that character and in the construction of the pinned Rankin–Selberg data for the Langlands–Tunnell argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_exists_isAdmissibleTwist_eulerCoeff_eq_inducedE3_of_finrank_eq_three.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import Definitions.Def_LanglandsTunnell_CubicLambda

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField NumberField.TateGlobal LanglandsTunnell.Converse LanglandsTunnell.RankinSelberg
  LanglandsTunnell.CubicLambda

theorem LanglandsTunnell.CubicInduction.exists_isAdmissibleTwist_eulerCoeff_eq_inducedE3_of_finrank_eq_three
    (K : Type) [Field K] [NumberField K] [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
    (hdeg : Module.finrank ℚ K = 3)
    (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (hμ : IsAdmissibleTwist K μ) :
    ∃ ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ, IsAdmissibleTwist ℚ ω ∧
      (∀ p : HeightOneSpectrum (𝓞 ℚ), ¬ IsBadPlace K μ p →
        IsUnramifiedCharAt ω p ∧ eulerCoeff ℚ ω p = inducedE3 ℚ (inducedCoeff K μ) p) ∧
      ∀ (uR : ∀ w : InfinitePlace K, w.IsReal → ℂ) (aR : ∀ w : InfinitePlace K, w.IsReal → ZMod 2)
        (uC : ∀ w : InfinitePlace K, w.IsComplex → ℂ) (kC : ∀ w : InfinitePlace K, w.IsComplex → ℤ),
        (∀ w, ∀ hw : w.IsReal, IsArchCompAt K μ w (uR w hw) ((aR w hw).val : ℤ)) →
        (∀ w, ∀ hw : w.IsComplex, IsArchCompAt K μ w (uC w hw) (kC w hw)) →
        ∀ v : InfinitePlace ℚ, v.IsReal →
          IsArchCompAt ℚ ω v
            ((∑ᶠ (w) (hw : w.IsReal), uR w hw) + (∑ᶠ (w) (hw : w.IsComplex), 2 * uC w hw))
            ((∑ᶠ (w) (hw : w.IsReal), ((aR w hw).val : ℤ)) + (∑ᶠ (w) (hw : w.IsComplex), (kC w hw + 1))) := by sorry
