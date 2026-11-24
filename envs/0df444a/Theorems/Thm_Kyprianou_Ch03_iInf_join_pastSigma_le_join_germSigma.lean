-- Prove2me | Theorems.Thm_Kyprianou_Ch03_iInf_join_pastSigma_le_join_germSigma
-- name    : Kyprianou.Ch03.iInf_join_pastSigma_le_join_germSigma
-- status  : Open
-- author  : @pageman
-- created : 2026-11-24T04:14:01.132672+00:00
-- url     : https://prove2.me/theorems/2eaa871c-f3d4-4f6a-8d83-e6bebd5cc673
-- title:
--   Infimum of joins with past filtrations lands in join with germ
-- statement:
--   Let $G$ be a $\sigma$-algebra on $\Omega$ and let $Y$ be a real process. Write $\mathcal{H}_\varepsilon=\sigma(Y_u:u\le\varepsilon)$ and $\mathcal{H}_{0+}=\bigcap_{\varepsilon>0}\mathcal{H}_\varepsilon$ for the germ of $Y$ at $0$.
--
--   Then
--   $$
--   \bigcap_{\varepsilon>0}\bigl(G\vee\mathcal{H}_\varepsilon\bigr) \;\subseteq\; G\vee\mathcal{H}_{0+}.
--   $$
--
--   This lattice identity is the remaining step after decomposing the raw natural filtration past time $t$ as $G_t\vee\mathcal{H}_\varepsilon$ for the shifted increment process. It is classical when $G$ is countably generated (second-countable codomain).
-- source:
--   Kyprianou (2006), Chapter 3, Exercise 3.1 (lattice step ∩(G∨H_ε)⊆G∨H_{0+}); cf. Dellacherie–Meyer / Durrett germ calculus

import Mathlib
import Definitions.Def_DurrettProbability_Brownian
open MeasureTheory ProbabilityTheory DurrettProbability
open scoped NNReal
set_option autoImplicit false

namespace Kyprianou.Ch03
theorem iInf_join_pastSigma_le_join_germSigma
    {Omega : Type} [MeasurableSpace Omega]
    (G : MeasurableSpace Omega)
    (Y : NNReal -> Omega -> Real) :
    (⨅ ε : NNReal, ⨅ (_ : 0 < ε), G ⊔ pastSigma Y ε) ≤ G ⊔ germSigma Y := by
  sorry

end Kyprianou.Ch03
