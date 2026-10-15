-- Prove2me | Theorems.Thm_Multihoming_Thresholds_price_lower_iff
-- name    : Multihoming.Thresholds.price_lower_iff
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T06:26:41.074984+00:00
-- url     : https://prove2.me/theorems/b7ad45cd-5bd2-4b8d-80d6-84008015e32b
-- title:
--   PDF p. 20 (printed p. 14) — the symmetric price is lower with network effects iff e > e_p = 2(t − μ)
-- statement:
--   Let $t>0$ and $0<\mu<t$, and let $p^M(\mu)=(t-\mu)(\mu+e)/(2t-\mu)$ be the symmetric partial-multihoming price (26), so that without network effects $p^M(0)=e/2$. With the price threshold $e_p\equiv 2(t-\mu)$,
--   $$e>e_p\iff p^M(\mu)<p^M(0).$$
--
--   This is the price half of Proposition 2: network effects lower the price exactly when the goods have many exclusive features.
--
--   **Formalization Note** The paper's sentence states the direction "$e>e_p \Rightarrow$ lower"; the equivalence is the form the paper's own computation gives and is posed here. Network effects are strict, $\mu>0$; at $\mu=0$ both prices coincide.
-- source:
--   Foros, Kind & Stähler, Endogenous multihoming and network effects: PlayStation, Xbox, or both?, SNF Working Paper No. 16/21 (NHH Bergen, December 2021; Management Science DOI 10.1287/mnsc.2022.00613), PDF p. 20 (printed p. 14), sentence after (26) defining e_p ≡ 2(t − μ)

import Mathlib
import Definitions.Def_Multihoming_Thresholds_Model

namespace Multihoming.Thresholds

theorem price_lower_iff (t μ e : ℝ) (ht : 0 < t) (hμ : 0 < μ) (hμt : μ < t) :
    eP t μ < e ↔ pM t μ e < pM t 0 e := by sorry

end Multihoming.Thresholds
