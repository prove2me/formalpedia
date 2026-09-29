-- Prove2me | Theorems.Thm_LanglandsTunnell_TateLocal_integrableOn_charExt_mul_norm_inv_and_exists_forall_setIntegral_psiLocal_mul_eq_add_mul_inv_of_lt_zero
-- name    : LanglandsTunnell.TateLocal.integrableOn_charExt_mul_norm_inv_and_exists_forall_setIntegral_psiLocal_mul_eq_add_mul_inv_of_lt_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:09.28874+00:00
-- url     : https://prove2.me/theorems/692bd1f8-4b29-58ca-89e3-eb8e19505a95
-- title:
--   Fourier tail of a negative-exponent quasi-character
-- statement:
--   Fix a height-one prime $p$ of the ring of integers of $\mathbb{Q}$ and write $F = \mathbb{Q}_p$ for the $p$-adic completion, carrying its valuation $v$ with values in $\mathbb{Z}_{m0}$ and the associated norm. Let $\eta : F^\times \to \mathbb{C}^\times$ be a locally constant group homomorphism, and let $\sigma$ be a real number with $\sigma < 0$ such that $\|\eta(a)\| = \|a\|^{\sigma}$ for every $a \in F^\times$; fix an integer $n_0$, and let $R = \{t \in F : \mathrm{WithZero.exp}\, n_0 \le v(t)\}$, the exterior region where the norm is bounded below (so $0 \notin R$). Equip $F$ with its Borel $\sigma$-algebra. The assertion is that for every additive Haar measure $\nu$ on $F$ two things hold. First, the function $t \mapsto \mathrm{charExt}\,\eta(t)\cdot \|t\|^{-1}$, where $\mathrm{charExt}\,\eta$ is $\eta$ extended by $0$ at the origin, is $\nu$-integrable on $R$. Second, there are a real $c > 0$ and complex numbers $A$, $B$ such that for every $y \in F^\times$ with $\|y\| \le c$, $$\int_{R} \psi(yt)\,\mathrm{charExt}\,\eta(t)\,\|t\|^{-1}\, d\nu(t) = A + B\,\eta(y)^{-1},$$ where $\psi = \mathrm{psiLocal}\ \mathbb{Q}\ p$ is the standard additive character of $F$, obtained by composing the additive embedding of $F$ as the component at $p$ of the adele ring of $\mathbb{Q}$ with the standard adelic additive character. The constants $c$, $A$, $B$ may depend on $\nu$.
--
--   This is the local Tate-integral estimate for the tail of a quasi-character of negative real exponent twisted by $\|t\|^{-1}$: off a ball the Fourier transform in the second variable collapses, for $y$ small, to a two-term expression $A + B\,\eta(y)^{-1}$, with no Gauss sums and no ramified/unramified case distinction. It is used in the evaluation of the local Jacquet integral for a principal series, via [`LanglandsTunnell.RankinSelberg.exists_forall_jacquetIntegral_diagOne_mul_eq_sqrt_modulus_mul_add_of_mem_principalSeries2_of_chamber`](thm.html#LanglandsTunnell.RankinSelberg.exists_forall_jacquetIntegral_diagOne_mul_eq_sqrt_modulus_mul_add_of_mem_principalSeries2_of_chamber).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_TateLocal_integrableOn_charExt_mul_norm_inv_and_exists_forall_setIntegral_psiLocal_mul_eq_add_mul_inv_of_lt_zero.lean

import Mathlib
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField MeasureTheory LanglandsTunnell.TateLocal

theorem LanglandsTunnell.TateLocal.integrableOn_charExt_mul_norm_inv_and_exists_forall_setIntegral_psiLocal_mul_eq_add_mul_inv_of_lt_zero
    (p : HeightOneSpectrum (𝓞 ℚ))
    (η : (p.adicCompletion ℚ)ˣ →* ℂˣ) (hη : IsLocallyConstant η)
    (σ : ℝ) (hσ : ∀ a : (p.adicCompletion ℚ)ˣ, ‖((η a : ℂˣ) : ℂ)‖ = ‖(a : p.adicCompletion ℚ)‖ ^ σ)
    (hσ0 : σ < 0) (n₀ : ℤ) :
    letI := localBorel ℚ p
    ∀ (ν : Measure (p.adicCompletion ℚ)) [ν.IsAddHaarMeasure],
      IntegrableOn (fun t : p.adicCompletion ℚ => charExt η t * ((‖t‖⁻¹ : ℝ) : ℂ))
          {t : p.adicCompletion ℚ | WithZero.exp n₀ ≤ Valued.v t} ν ∧
      ∃ (c : ℝ) (A B : ℂ), 0 < c ∧
        ∀ y : (p.adicCompletion ℚ)ˣ, ‖(y : p.adicCompletion ℚ)‖ ≤ c →
          ∫ t in {t : p.adicCompletion ℚ | WithZero.exp n₀ ≤ Valued.v t},
              NumberField.StandardAddChar.psiLocal ℚ p ((y : p.adicCompletion ℚ) * t) *
                (charExt η t * ((‖t‖⁻¹ : ℝ) : ℂ)) ∂ν =
            A + B * (((η y : ℂˣ) : ℂ))⁻¹ := by sorry
