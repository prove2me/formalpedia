-- Prove2me | Theorems.Thm_LanglandsTunnell_RankinSelberg_map_bigCellWeyl_withDensity_eq_pi_selfDualHaarAt
-- name    : LanglandsTunnell.RankinSelberg.map_bigCellWeyl_withDensity_eq_pi_selfDualHaarAt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:09.28874+00:00
-- url     : https://prove2.me/theorems/3f96cfe6-b3af-5dfa-8031-fcf2bf6eaadf
-- title:
--   Big-cell Weyl coordinates push additive Haar onto M₂(ℚₚ)
-- statement:
--   Let $p$ be a height-one prime of the ring of integers of $\mathbb{Q}$ and let $F = \mathbb{Q}_p$ denote the $p$-adic completion, carried with the Borel $\sigma$-algebra `localBorel` of its valuation topology. Write $dx$ for `selfDualHaarAt ℚ p`, the additive Haar measure normalising the ring of integers by the factor $(\mathrm{absNorm}\,p)^{-\mathrm{level}(\psi)/2}$, where $\psi$ is the local component at $p$ of the standard additive character and its level is the supremum of the $n \in \mathbb{Z}$ with $\psi$ trivial on $\{|x| \le q^{-n}\}$; write $|\cdot|$ for `modulus`, the module of multiplication by a nonzero scalar (and $0$ at $0$); and write $d^\times x$ for the measure on $F^\times$ obtained by pulling back along `Units.val` the measure $dx$ restricted to $F \setminus \{0\}$ with density $|x|^{-1}$. The assertion is that the pushforward along $$(b,x,a,y) \longmapsto \begin{pmatrix} bx & b(xy+a) \\ -b & -by\end{pmatrix},\qquad (b,x,a,y) \in F^\times \times F \times F^\times \times F,$$ of the measure $d^\times b\,dx\,d^\times a\,dy$ weighted by the density $|b|^4\,|a|$ (valued in $\mathbb{R}_{\ge 0}^\infty$) equals the fourfold product measure $\prod_{i,j \in \{0,1\}} dx$ on $\mathrm{Fin}\,2 \to \mathrm{Fin}\,2 \to F$, i.e. additive Haar measure on $M_2(F)$ normalised as the product of four copies of $dx$.
--
--   This is the Jacquet–Langlands big-cell change of variables, writing almost every matrix in the form $b\,n(-x)\,\mathrm{diag}(a,1)\,w\,n(y)$ and recording the resulting Jacobian $|b|^4|a|$ relating $d^\times b\,dx\,d^\times a\,dy$ to additive Haar measure on $M_2(F)$. It feeds the local Rankin–Selberg computation, being used in [`LanglandsTunnell.RankinSelberg.matFourier22_kirillov_det_mul_coefficient_eq_of_cuspidal`](thm.html#LanglandsTunnell.RankinSelberg.matFourier22_kirillov_det_mul_coefficient_eq_of_cuspidal) to convert integrals over $M_2(\mathbb{Q}_p)$ into integrals in Kirillov-type coordinates.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_RankinSelberg_map_bigCellWeyl_withDensity_eq_pi_selfDualHaarAt.lean

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

theorem LanglandsTunnell.RankinSelberg.map_bigCellWeyl_withDensity_eq_pi_selfDualHaarAt
    (p : HeightOneSpectrum (𝓞 ℚ)) :
    letI : MeasurableSpace (p.adicCompletion ℚ) := localBorel ℚ p
    MeasureTheory.Measure.map (β := Fin 2 → Fin 2 → p.adicCompletion ℚ)
        (fun q : (p.adicCompletion ℚ)ˣ × p.adicCompletion ℚ × (p.adicCompletion ℚ)ˣ × p.adicCompletion ℚ =>
          !![(q.1 : p.adicCompletion ℚ) * q.2.1, (q.1 : p.adicCompletion ℚ) * (q.2.1 * q.2.2.2 + (q.2.2.1 : p.adicCompletion ℚ));
             -(q.1 : p.adicCompletion ℚ), -((q.1 : p.adicCompletion ℚ) * q.2.2.2)])
        (((MeasureTheory.Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))).prod
            ((selfDualHaarAt ℚ p).prod
              ((MeasureTheory.Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))).prod (selfDualHaarAt ℚ p)))).withDensity
          fun q => (modulus (q.1 : p.adicCompletion ℚ) : ℝ≥0∞) ^ 4 * (modulus (q.2.2.1 : p.adicCompletion ℚ) : ℝ≥0∞)) =
      (MeasureTheory.Measure.pi fun _ : Fin 2 => MeasureTheory.Measure.pi fun _ : Fin 2 => selfDualHaarAt ℚ p) := by sorry
