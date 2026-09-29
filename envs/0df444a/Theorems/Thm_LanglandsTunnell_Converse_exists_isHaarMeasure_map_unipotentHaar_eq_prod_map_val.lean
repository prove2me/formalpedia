-- Prove2me | Theorems.Thm_LanglandsTunnell_Converse_exists_isHaarMeasure_map_unipotentHaar_eq_prod_map_val
-- name    : LanglandsTunnell.Converse.exists_isHaarMeasure_map_unipotentHaar_eq_prod_map_val
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:02.424499+00:00
-- url     : https://prove2.me/theorems/c4b2cce4-84f6-5002-a143-b73e6f65bce8
-- title:
--   Haar splitting of the adelic unipotent group of GL₂/ℚ
-- statement:
--   Give $\mathrm{GL}_2(\mathbb{R})$ and $\mathrm{GL}_2$ of the adele ring of $\mathbb{Q}$ their Borel $\sigma$-algebras. The assertion is that there exist measures $\mu_{N,\infty}$ on [`RSCarrier.realUnipotent`](def/LanglandsTunnell_RSCarrier.html#L24), the image of `unipotentGL2Hom` over $\mathbb{R}$, i.e. the subgroup $\{\begin{pmatrix}1&x\\0&1\end{pmatrix}\}$ of $\mathrm{GL}_2(\mathbb{R})$, and $\mu_{N,\mathrm{fin}}$ on [`RSCarrier.finUnipotent`](def/LanglandsTunnell_RSCarrier.html#L43), the subgroup of `finiteAdelicGL2Subgroup ℚ` (the kernel of the archimedean projection `glArch`) induced by `adelicUnipotent ℚ`, both Haar measures, such that the following holds. Let `unipotentHaar ℚ` be the measure on `adelicUnipotent ℚ` obtained by transporting, along $x \mapsto \begin{pmatrix}1&x\\0&1\end{pmatrix}$, the additive Haar measure of the adeles of $\mathbb{Q}$ rescaled by the inverse of the volume of the adelic box. Its image under the map sending $n$ to the pair consisting of [`LanglandsTunnell.ratArchGL2 n`](def/LanglandsTunnell_DeltaLift.html#L16), the component of $n$ at the unique infinite place read in $\mathrm{GL}_2(\mathbb{R})$ through the isomorphism of that completion with $\mathbb{R}$, and of [`RSCarrier.finFactor n`](def/LanglandsTunnell_RSCarrierSplit.html#L17), namely the product of the inverse of the archimedean embedding of `ratArchGL2 n` with $n$, which lies in `finiteAdelicGL2Subgroup ℚ`, equals the product of the pushforwards of $\mu_{N,\infty}$ and $\mu_{N,\mathrm{fin}}$ along the respective subgroup inclusions.
--
--   This is the product decomposition of Haar measure on the unipotent radical of the adelic Borel subgroup of $\mathrm{GL}_2$ over $\mathbb{Q}$, along the splitting of the adeles into their real and finite parts. It supplies the measure-theoretic normalisation used when Rankin–Selberg integrals over the adelic group are factored into an archimedean integral and a finite-adelic integral.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_Converse_exists_isHaarMeasure_map_unipotentHaar_eq_prod_map_val.lean

import Definitions.Def_AutomorphicForm_UnipotentQuotient
import Definitions.Def_LanglandsTunnell_DeltaLift
import Definitions.Def_LanglandsTunnell_RSCarrier
import Definitions.Def_LanglandsTunnell_RSCarrierSplit

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField AutomorphicForm MeasureTheory

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem LanglandsTunnell.Converse.exists_isHaarMeasure_map_unipotentHaar_eq_prod_map_val :
    letI : MeasurableSpace (GL (Fin 2) ℝ) := borel (GL (Fin 2) ℝ)
    ∃ (μNArch : Measure RSCarrier.realUnipotent) (μNFin : Measure RSCarrier.finUnipotent),
      μNArch.IsHaarMeasure ∧ μNFin.IsHaarMeasure ∧
        Measure.map
            (fun n : adelicUnipotent ℚ => (LanglandsTunnell.ratArchGL2 n, RSCarrier.finFactor n))
            (unipotentHaar ℚ) =
          (Measure.map Subtype.val μNArch).prod (Measure.map Subtype.val μNFin) := by sorry
