-- Prove2me | Theorems.Thm_LanglandsTunnell_TateLocal_setIntegral_psiLocal_mul_charExt_inv_mul_cpow_eq_charExt_mul_stdRootNumberAt
-- name    : LanglandsTunnell.TateLocal.setIntegral_psiLocal_mul_charExt_inv_mul_cpow_eq_charExt_mul_stdRootNumberAt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:10.196979+00:00
-- url     : https://prove2.me/theorems/b823fe34-a166-5559-91cb-9a67124bad64
-- title:
--   Tate's Gauss-sum formula for the standard local root number
-- statement:
--   Let $K$ be a number field, $v$ a nonzero prime of $\mathcal O_K$, and $\chi$ a monoid homomorphism from the units of the completion $K_v$ to $\mathbb C^\times$. Let $a$ be a natural number with $1 \le a$ such that `HasConductorExponentAt K v χ a` holds, i.e. $\chi$ is trivial on `higherUnitsAt K v a` — the units $u$ with $\mathrm{v}(u) = 1$ and either $a = 0$ or $\mathrm{v}(u - 1) \le \exp(-a)$ — while for every $m < a$ some element of `higherUnitsAt K v m` is not killed by $\chi$; assume moreover $|\chi(\varpi_v)| = 1$ for the distinguished uniformizer unit `uniformizerUnit K v`. Write $n$ for `addCharLevel (psiLocal K v)`, the supremum of the integers $m$ with $\psi_{K,v}$ trivial on $\{x : \mathrm{v}(x) \le \exp m\}$, where $\psi_{K,v}$ is the standard adelic additive character composed with the inclusion of $K_v$ at $v$. Let $z \in K_v$ satisfy $\mathrm{v}(z) = \exp(n + a)$. Then, with $K_v$ given its Borel $\sigma$-algebra, the integral of $u \mapsto \psi_{K,v}(zu)\,\chi^{-1}(u)$ (with $\chi^{-1}$ extended by $0$ at $0$ via `charExt`) over $\{u : \mathrm{v}(u) = 1\}$, against the self-dual measure `selfDualHaarAt K v` (the Haar measure giving the valuation ring mass $N(v)^{-n/2}$), multiplied by $N(v)^{(n+a)/2}$ as a complex power of the absolute norm of $v$, equals $\chi(z) \cdot$ `stdRootNumberAt K v χ`, the standard local $\varepsilon$-factor of $\chi$ at $s = 1/2$.
--
--   This is Tate's evaluation of the local $\varepsilon$-factor of a ramified character as a normalised Gauss integral over the critical shell, for the standard additive character and self-dual measure. It is used in the construction of Whittaker models, where the value of a local Whittaker function on the shell of valuation $n+a$ is identified with the standard local root number.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_TateLocal_setIntegral_psiLocal_mul_charExt_inv_mul_cpow_eq_charExt_mul_stdRootNumberAt.lean

import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory IsDedekindDomain NumberField NumberField.StandardAddChar NumberField.AdelicLevel
  LanglandsTunnell.TateLocal

theorem LanglandsTunnell.TateLocal.setIntegral_psiLocal_mul_charExt_inv_mul_cpow_eq_charExt_mul_stdRootNumberAt
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    (χ : (v.adicCompletion K)ˣ →* ℂˣ) (a : ℕ) (ha : 1 ≤ a) (hχ : HasConductorExponentAt K v χ a)
    (hχu : ‖(χ (uniformizerUnit K v) : ℂ)‖ = 1)
    (z : v.adicCompletion K) (hz : Valued.v z = WithZero.exp (addCharLevel (psiLocal K v) + a)) :
    letI := localBorel K v
    (∫ u in {u : v.adicCompletion K | Valued.v u = 1}, psiLocal K v (z * u) * charExt χ⁻¹ u
        ∂(selfDualHaarAt K v)) *
      (Ideal.absNorm v.asIdeal : ℂ) ^ (((addCharLevel (psiLocal K v) + a : ℤ) : ℂ) / 2)
      = charExt χ z * stdRootNumberAt K v χ := by sorry
