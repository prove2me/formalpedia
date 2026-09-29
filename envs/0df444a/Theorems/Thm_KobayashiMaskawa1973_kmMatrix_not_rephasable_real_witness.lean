-- Prove2me | Theorems.Thm_KobayashiMaskawa1973_kmMatrix_not_rephasable_real_witness
-- name    : KobayashiMaskawa1973.kmMatrix_not_rephasable_real_witness
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-09-24T18:12:46.715161+00:00
-- url     : https://prove2.me/theorems/09c84702-7bb0-448b-a354-a2974791721d
-- title:
--   Kobayashi--Maskawa matrix with phase cannot be rephased to a real matrix
-- statement:
--   For the explicit parameter choice $\theta_1 = \theta_2 = \theta_3 = \pi/4$ and $\delta = \pi/2$, the Kobayashi--Maskawa mixing matrix $K$ cannot be made real by any choice of field phase conventions:
--
--   $$\text{for every } V \text{ rephasing-equivalent to } K, \quad \neg \text{IsRealMatrix } V.$$
--
--   Under any rephasing $V = \operatorname{diag}(e^{ia}) K \operatorname{diag}(e^{ib})$ with real phases $a, b \in \mathbb{R}^3$, the quartet product (Jarlskog invariant) satisfies:
--
--   $$\operatorname{Im}(V_{00} V_{11} V_{01}^* V_{10}^*) = \operatorname{Im}(K_{00} K_{11} K_{01}^* K_{10}^*) = c_1 c_2 c_3 s_1^2 s_2 s_3 \sin\delta = \frac{1}{8\sqrt{2}} \neq 0.$$
--
--   Since any real matrix $V$ would have all entries real and hence $\operatorname{Im}(V_{00} V_{11} V_{01}^* V_{10}^*) = 0$, no such rephasing can produce a real matrix. This proves Kobayashi and Maskawa's central discovery: six quark fields (three doublets) allow an irreducible CP-violating phase that cannot be eliminated by field redefinitions.
-- source:
--   M. Kobayashi and T. Maskawa, Progress of Theoretical Physics 49 (1973) 652-657, pp. 654

import Mathlib
import Definitions.Def_KobayashiMaskawa1973_Defs

open Matrix

namespace KobayashiMaskawa1973

theorem kmMatrix_not_rephasable_real_witness :
    ∀ V : Matrix (Fin 3) (Fin 3) ℂ,
      RephasingEquiv (kmMatrix (Real.pi / 4) (Real.pi / 4) (Real.pi / 4) (Real.pi / 2)) V →
      ¬ IsRealMatrix V := by sorry

end KobayashiMaskawa1973
