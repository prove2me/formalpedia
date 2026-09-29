-- Prove2me | Theorems.Thm_LanglandsTunnell_RankinSelberg_setIntegral_translate_transposeTwist_eq_mul_sum_of_forall_setIntegral_translate_eq
-- name    : LanglandsTunnell.RankinSelberg.setIntegral_translate_transposeTwist_eq_mul_sum_of_forall_setIntegral_translate_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:09.28874+00:00
-- url     : https://prove2.me/theorems/551406cc-8d6b-58e1-97fc-7988c1a798ef
-- title:
--   Twisted contragredient transport of a separated family
-- statement:
--   Fix a nonzero prime $p$ of the ring of integers of $\mathbb{Q}$ and write $F =$ `p.adicCompletion ℚ` for the associated completion. Let $\Omega$ be a subgroup of $\mathrm{GL}_2(F)$ whose underlying set is compact (`hΩc`) and which is stable under the transpose-inverse map `transposeInvN`, $\omega \mapsto {}^{t}(\omega^{-1})$ (`hΩt`). Let $w : \mathrm{GL}_2(F) \to \mathbb{C}$ be a function, $\iota$ a finite index type, and $w_j, c_j : \mathrm{GL}_2(F) \to \mathbb{C}$ ($j \in \iota$) two families of functions; fix $a, d \in \mathrm{GL}_2(F)$. Equip $\mathrm{GL}_2(F)$ with the Borel $\sigma$-algebra `localGLBorel` and the matching Borel space structure. The assertion is that for every Haar measure $\mu_2$ on $\mathrm{GL}_2(F)$, if the separation identity $\int_\Omega w(g\,\omega\,h)\,d\mu_2(\omega) = \mu_2(\Omega)\sum_{j} c_j(h)\,w_j(g)$ holds for all $g, h \in \mathrm{GL}_2(F)$ (with $\mu_2(\Omega)$ read as a real number and then as a complex scalar), then for all $g, h$ one has $$\int_\Omega \lvert\det(d g \omega h)\rvert \, w\bigl(a\cdot{}^{t}((d g \omega h)^{-1})\bigr)\,d\mu_2(\omega) = \mu_2(\Omega) \sum_{j} \Bigl(\lvert\det h\rvert\, c_j\bigl({}^{t}(h^{-1})\bigr)\Bigr)\Bigl(\lvert\det (dg)\rvert\, w_j\bigl(a\cdot{}^{t}((dg)^{-1})\bigr)\Bigr),$$ where $\lvert\cdot\rvert$ denotes `modulus`, the scaling factor of the element on a Haar measure of $F$, which on $F$ coincides with the $p$-adic norm. No measurability or integrability assumption on $w$, $w_j$ or $c_j$ is imposed.
--
--   This is the local statement that the twisted contragredient operation $w \mapsto \bigl(g \mapsto \lvert\det(dg)\rvert\, w(a\,{}^{t}(dg)^{-1})\bigr)$ carries a family separating the $\Omega$-average of $w$ into a family of the same shape, with $c_j$ replaced by $h \mapsto \lvert\det h\rvert\, c_j({}^{t}h^{-1})$; it is the bookkeeping behind the dual side of a local Rankin–Selberg integral. It is used in the construction of local Rankin–Selberg integrals for the Jacquet–Whittaker function, in [`LanglandsTunnell.RankinSelberg.exists_rsLocalIntegral_jacquetWhittaker3_iotaGL_eq_sum_and_dual_eq_mul_sum_of_chamber_ed2`](thm.html#LanglandsTunnell.RankinSelberg.exists_rsLocalIntegral_jacquetWhittaker3_iotaGL_eq_sum_and_dual_eq_mul_sum_of_chamber_ed2), and rests on the invariance of Haar measure on $\mathrm{GL}_2(F)$ under transpose-inverse.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_RankinSelberg_setIntegral_translate_transposeTwist_eq_mul_sum_of_forall_setIntegral_translate_eq.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_GodementSection
import Definitions.Def_LanglandsTunnell_CubicInduction_LocalZeta31
import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries2
import Definitions.Def_LanglandsTunnell_RSCarrier
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_AdelicDock_LocalEmbedding

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField MeasureTheory AutomorphicForm LanglandsTunnell.TateLocal
  LanglandsTunnell.CubicInduction NumberField.StandardAddChar
open NumberField.AdelicLevel (diagOne)

theorem LanglandsTunnell.RankinSelberg.setIntegral_translate_transposeTwist_eq_mul_sum_of_forall_setIntegral_translate_eq
    (p : HeightOneSpectrum (𝓞 ℚ))
    (Ω : Subgroup (GL (Fin 2) (p.adicCompletion ℚ))) (hΩc : IsCompact (Ω : Set (GL (Fin 2) (p.adicCompletion ℚ))))
    (hΩt : ∀ ω ∈ Ω, transposeInvN (Fin 2) ω ∈ Ω)
    (w : GL (Fin 2) (p.adicCompletion ℚ) → ℂ) (ι : Type) [Fintype ι] (wj : ι → GL (Fin 2) (p.adicCompletion ℚ) → ℂ) (c : ι → GL (Fin 2) (p.adicCompletion ℚ) → ℂ)
    (a d : GL (Fin 2) (p.adicCompletion ℚ)) :
    letI := localGLBorel ℚ p
    haveI := borelSpace_localGLBorel ℚ p
    ∀ (μ₂ : Measure (GL (Fin 2) (p.adicCompletion ℚ))) [μ₂.IsHaarMeasure],
      (∀ g h : GL (Fin 2) (p.adicCompletion ℚ),
        ∫ ω in (Ω : Set (GL (Fin 2) (p.adicCompletion ℚ))), w (g * ω * h) ∂μ₂ =
          ((μ₂ (Ω : Set (GL (Fin 2) (p.adicCompletion ℚ)))).toReal : ℂ) * ∑ j, c j h * wj j g) →
      ∀ g h : GL (Fin 2) (p.adicCompletion ℚ),
        ∫ ω in (Ω : Set (GL (Fin 2) (p.adicCompletion ℚ))),
            (fun g : GL (Fin 2) (p.adicCompletion ℚ) => ((modulus ((Matrix.GeneralLinearGroup.det (d * g) : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ℝ) : ℂ) * w (a * transposeInvN (Fin 2) (d * g))) (g * ω * h) ∂μ₂ =
          ((μ₂ (Ω : Set (GL (Fin 2) (p.adicCompletion ℚ)))).toReal : ℂ) *
            ∑ j, (((modulus ((Matrix.GeneralLinearGroup.det h : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ℝ) : ℂ) * c j (transposeInvN (Fin 2) h)) *
              (((modulus ((Matrix.GeneralLinearGroup.det (d * g) : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ℝ) : ℂ) * wj j (a * transposeInvN (Fin 2) (d * g))) := by sorry
