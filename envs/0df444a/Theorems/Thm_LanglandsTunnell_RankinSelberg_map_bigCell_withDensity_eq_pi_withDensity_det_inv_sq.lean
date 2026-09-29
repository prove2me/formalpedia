-- Prove2me | Theorems.Thm_LanglandsTunnell_RankinSelberg_map_bigCell_withDensity_eq_pi_withDensity_det_inv_sq
-- name    : LanglandsTunnell.RankinSelberg.map_bigCell_withDensity_eq_pi_withDensity_det_inv_sq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:09.28874+00:00
-- url     : https://prove2.me/theorems/fd7f518a-d69e-55f2-914f-d605a6a5f129
-- title:
--   Big-cell coordinates: |a/b| measure pushes to |det X|⁻² dX
-- statement:
--   Let $p$ be a nonzero prime ideal of $\mathcal O_{\mathbb Q}$ and write $F = \mathbb Q_p$ for the completion $p.\mathrm{adicCompletion}\ \mathbb Q$, equipped with the Borel $\sigma$-algebra `localBorel` of its valuation topology. Let $dx =$ `selfDualHaarAt ℚ p` be the additive Haar measure on $F$ scaled by $(\mathrm{absNorm}\ p)^{-n/2}$, where $n$ is the level `addCharLevel (psiLocal ℚ p)` of the standard local additive character, relative to the Haar measure normalised by the ring of integers; let $d^{\times}t$ denote the measure on $F^{\times}$ obtained as the `Units.val`-comap of `mulMeasure` $dx$, that is of the restriction of $dx$ to $F \setminus \{0\}$ with density $t \mapsto |t|^{-1}$, where $|\cdot| =$ `modulus` is the module (equal to the norm, by `modulus_adicCompletion_eq_nnnorm`). On $F \times F^{\times} \times F^{\times} \times F$ take the product measure $dx \otimes d^{\times}b \otimes d^{\times}a \otimes dz$ with density $(x,b,a,z) \mapsto |a b^{-1}|$, and consider the map sending $(x,b,a,z)$ to the matrix underlying $\begin{pmatrix}1&0\\ z&1\end{pmatrix}\begin{pmatrix}a&0\\ 0&b\end{pmatrix}\begin{pmatrix}1&x\\ 0&1\end{pmatrix}$ in $GL_2(F)$. The assertion is that the pushforward of this weighted measure equals the fourfold product measure $\bigotimes_{i,j \in \mathrm{Fin}\,2} dx$ on $\mathrm{Fin}\,2 \to \mathrm{Fin}\,2 \to F$ with density the indicator of $\{X : \det X \neq 0\}$ times $(|\det X|^{2})^{-1}$, as $\mathbb R_{\geq 0}^{\infty}$-valued densities. Only this equality of measures is asserted; no injectivity or surjectivity statement about the parametrisation is part of the conclusion.
--
--   This is the local computation, in Bruhat big-cell coordinates $n^{-}(z)\,\mathrm{diag}(a,b)\,n(x)$, comparing the measure $|a/b|\,dx\,d^{\times}b\,d^{\times}a\,dz$ on the cell with the measure $|\det X|^{-2}\,dX$ on $M_2(F)$, the latter being the Haar measure of $GL_2(F)$ written in the coordinates of the ambient matrix algebra. It is used in the Rankin–Selberg local theory, where it feeds the comparison of an integral against a Haar measure on $GL_2(F)$ with an integral against the matrix measure weighted by $|\det|^{-2}$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_RankinSelberg_map_bigCell_withDensity_eq_pi_withDensity_det_inv_sq.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_GodementSection
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_AutomorphicForm_ArchDerivCasimir
import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField MeasureTheory AutomorphicForm LanglandsTunnell.TateLocal LanglandsTunnell.CubicInduction
open scoped ENNReal

theorem LanglandsTunnell.RankinSelberg.map_bigCell_withDensity_eq_pi_withDensity_det_inv_sq
    (p : HeightOneSpectrum (𝓞 ℚ)) :
    letI : MeasurableSpace (p.adicCompletion ℚ) := localBorel ℚ p
    MeasureTheory.Measure.map (β := Fin 2 → Fin 2 → p.adicCompletion ℚ)
        (fun q : p.adicCompletion ℚ × (p.adicCompletion ℚ)ˣ × (p.adicCompletion ℚ)ˣ × p.adicCompletion ℚ =>
          ((lowerUnipotentGL2 q.2.2.2 * diagUnits2 q.2.2.1 q.2.1 * unipotentGL2 q.1 : GL (Fin 2) (p.adicCompletion ℚ)) :
            Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)))
        (((selfDualHaarAt ℚ p).prod
            ((MeasureTheory.Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))).prod
              ((MeasureTheory.Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))).prod (selfDualHaarAt ℚ p)))).withDensity
          fun q => (modulus (((q.2.2.1 * (q.2.1)⁻¹ : (p.adicCompletion ℚ)ˣ)) : p.adicCompletion ℚ) : ℝ≥0∞)) =
      (MeasureTheory.Measure.pi fun _ : Fin 2 => MeasureTheory.Measure.pi fun _ : Fin 2 => selfDualHaarAt ℚ p).withDensity
        fun X : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ) =>
          {X : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ) | X.det ≠ 0}.indicator
            (fun X => (((modulus X.det : ℝ≥0∞)) ^ 2)⁻¹) X := by sorry
