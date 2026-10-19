-- Prove2me | Theorems.Thm_OAI_AsymptoticallyMinimalLittlewood_Packing_packing_eventual_parameters
-- name    : OAI.AsymptoticallyMinimalLittlewood.Packing.packing_eventual_parameters
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T05:37:37.397532+00:00
-- url     : https://prove2.me/theorems/44e5939b-3e50-443d-afb5-f6455d13a4d8
-- title:
--   Eventual validity of the slot-packing parameter inequalities for large moduli
-- statement:
--   Let $r,L,R$ be natural numbers with $L>0$ and $R>0$, and let $e>0$, $p>0$, $\eta$, $t$, $T$ be real numbers. Write $\rho=r-1$ (difference of natural numbers, truncated at $0$). For a natural number $q$ let
--   $$K_q=\Big\lfloor\frac{q-1}{2RL}\Big\rfloor,\qquad\kappa_q=\frac{K_q}{q},$$
--   and define
--   $$A_q=3\Big[2\Big(\rho\big(1-2(R-2)L\kappa_q\big)+\frac{2\rho^2(2RL+1)}{q}\Big)+\rho^2\Big(1-2(R-2)L\kappa_q+\frac{2(R-2)L}{q}\Big)\Big],$$
--   $$N_q=r(R-1)\kappa_q,\qquad B_q=\frac{r\max(A_q,0)}{(ep/2)^2},$$
--   where $R-2$ and $R-1$ are real differences, together with the limiting values
--   $$N_\infty=\frac{r(1-1/R)}{2L},\qquad B_\infty=\frac{r}{(ep/2)^2}\cdot\frac{6(2\rho+\rho^2)}{R}.$$
--   Assume
--   $$B_\infty<\frac{ep}{2},\qquad N_\infty-B_\infty>0,\qquad N_\infty<r,\qquad rt<(1-\eta)(N_\infty-B_\infty).$$
--   Then for all sufficiently large natural numbers $q$:
--   1. $1/q\le ep$;
--   2. $T/q\le p$;
--   3. $T/q\le N_q-B_q$;
--   4. $B_q\le ep/2$;
--   5. $N_q\le r$;
--   6. $rt<(1-\eta)(N_q-B_q)$.
--
--   For the signed-slot construction modulo $q$ with $R$ periods per chunk and $K_q$ chunks, $A_q$ is the explicit bound on the mean-square deviation of slot densities, $qN_q$ is the number of slot vertices and $qB_q$ the resulting budget of vertices with atypical degree. The lemma transfers the strict inequalities satisfied by the limiting values to all sufficiently large moduli; after multiplication by $q$ they become the numerical hypotheses of the random matching step.
--
--   **Formalization Note** $K_q$ is `chunkCount (2*R*L) q`, computed with truncated subtraction and floor division of natural numbers; $A_q$, $N_q$, $B_q$, $N_\infty$, $B_\infty$ are `packingAV r L R q`, `packingNV r L R q`, `packingBV r L R e p q`, `packingNLimit r L R` and `packingBLimit r R e p`. "For all sufficiently large $q$" is an eventual statement along the `atTop` filter on the natural numbers.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Littlewood/SlotParameters.lean#L172-L194

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

theorem OAI.AsymptoticallyMinimalLittlewood.Packing.packing_eventual_parameters {r L R : ℕ} (hL : 0<L) (hR : 0<R)
    {e p η t T : ℝ} (he : 0<e) (hp : 0<p)
    (hB : packingBLimit r R e p<e*p/2)
    (hS : 0<packingNLimit r L R-packingBLimit r R e p)
    (hN : packingNLimit r L R<(r : ℝ))
    (hM : (r : ℝ)*t<(1-η)*(packingNLimit r L R-packingBLimit r R e p)) :
    ∀ᶠ q : ℕ in atTop,
      1/(q : ℝ)≤e*p ∧ T/(q : ℝ)≤p ∧
      T/(q : ℝ)≤packingNV r L R q-packingBV r L R e p q ∧
      packingBV r L R e p q≤e*p/2 ∧ packingNV r L R q≤(r : ℝ) ∧
      (r : ℝ)*t<(1-η)*(packingNV r L R q-packingBV r L R e p q) := by sorry
