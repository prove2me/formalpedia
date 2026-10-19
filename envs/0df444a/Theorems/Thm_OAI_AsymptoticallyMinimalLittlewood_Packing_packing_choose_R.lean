-- Prove2me | Theorems.Thm_OAI_AsymptoticallyMinimalLittlewood_Packing_packing_choose_R
-- name    : OAI.AsymptoticallyMinimalLittlewood.Packing.packing_choose_R
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T05:36:47.775398+00:00
-- url     : https://prove2.me/theorems/fbc01a41-7f5d-42fd-a9fe-ebf2dbd3e9c0
-- title:
--   Choosing the number of periods per chunk in the signed-slot packing
-- statement:
--   Let $r$ and $L$ be positive integers and let $e>0$, $p>0$, $\eta$ and $t$ be real numbers. For a natural number $R$ define, with $r-1$ the difference of natural numbers,
--   $$A_\infty(R)=\frac{6\big(2(r-1)+(r-1)^2\big)}{R},\qquad N_\infty(R)=\frac{r\,(1-1/R)}{2L},\qquad B_\infty(R)=\frac{r\,A_\infty(R)}{(ep/2)^2}.$$
--   Suppose that
--   $$rt<(1-\eta)\,\frac{r}{2L}.$$
--   Then there is an integer $R\ge3$ such that
--   1. $B_\infty(R)<ep/2$;
--   2. $N_\infty(R)-B_\infty(R)>0$;
--   3. $N_\infty(R)<r$;
--   4. $rt<(1-\eta)\big(N_\infty(R)-B_\infty(R)\big)$.
--
--   In the signed-slot packing with $R$ periods per chunk, $N_\infty(R)$ is the limiting number of slot vertices per residue as the prime modulus tends to infinity, and $B_\infty(R)$ is the corresponding limiting budget of vertices with atypical degree. The lemma fixes $R$ before the modulus is chosen, so that the error budget stays below the degree tolerance $ep/2$ and the matching produced by the nibble argument still has density above the target $t$.
--
--   **Formalization Note** $A_\infty$, $N_\infty$ and $B_\infty$ are `packingALimit r R`, `packingNLimit r L R` and `packingBLimit r R e p`; no sign condition is imposed on $\eta$ or $t$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Littlewood/SlotParameters.lean#L141-L170

import Mathlib
import Definitions.Def_AsymptoticallyMinimalLittlewood
import Definitions.Def_OAI_Analysis_Littlewood_Gaussian
import Definitions.Def_OAI_Analysis_Littlewood_Rounding
import Definitions.Def_OAI_Analysis_Littlewood_BinaryPacket
import Definitions.Def_OAI_Analysis_Littlewood_QuadraticTail
import Definitions.Def_OAI_Analysis_Littlewood_Spreading
import Definitions.Def_OAI_Analysis_Littlewood_ProductProbability
import Definitions.Def_OAI_Analysis_Littlewood_Nibble
import Definitions.Def_OAI_Analysis_Littlewood_Averages
import Definitions.Def_OAI_Analysis_Littlewood_FiniteRank
import Definitions.Def_OAI_Analysis_Littlewood_Chunks
import Definitions.Def_OAI_Analysis_Littlewood_DependentMoments
import Definitions.Def_OAI_Analysis_Littlewood_SlotGraph
import Definitions.Def_OAI_Analysis_Littlewood_SlotParameters

open OAI OAI.AsymptoticallyMinimalLittlewood OAI.AsymptoticallyMinimalLittlewood.Packing
universe uV
open Filter Topology
open scoped BigOperators

theorem OAI.AsymptoticallyMinimalLittlewood.Packing.packing_choose_R {r L : ℕ} (hr : 0<r) (hL : 0<L)
    {e p η t : ℝ} (he : 0<e) (hp : 0<p)
    (hmargin : (r : ℝ)*t<(1-η)*((r : ℝ)/(2*L))) :
    ∃ R : ℕ, 3≤R ∧
      packingBLimit r R e p<e*p/2 ∧
      0<packingNLimit r L R-packingBLimit r R e p ∧
      packingNLimit r L R<(r : ℝ) ∧
      (r : ℝ)*t<(1-η)*(packingNLimit r L R-packingBLimit r R e p) := by sorry
