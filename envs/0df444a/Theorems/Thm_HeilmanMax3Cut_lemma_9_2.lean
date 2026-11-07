-- Prove2me | Theorems.Thm_HeilmanMax3Cut_lemma_9_2
-- name    : HeilmanMax3Cut.lemma_9_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:34:22.327566+00:00
-- url     : https://prove2.me/theorems/e29cfd6d-509e-4d74-9394-d8c7b9c7e565
-- title:
--   Lemma 9.2 — closed forms of $u_*$ and $J_*$ through $F_v$
-- statement:
--   Fix $0<\sigma\le1/2$. With $u_*=K_*1$, $u_0=K_01$, $B^{(1)}$ (103), $J_*=J_0+B^{(1)}$ (104) and $F_v(t)$ (117), for every $t\ge0$:
--
--   1. $u_*(t)=u_0(t)+4B^{(1)}(t)$;
--   2. $J_*(t)=J_0(t)+B^{(1)}(t)$;
--   3. $\displaystyle u_0(t)=\frac12\int_0^{2/3}(2+3v)\,F_v(t)\,dv$;
--   4. $\displaystyle J_0(t)=\frac12\int_0^{2/3}(3v-1)\,F_v(t)\,dv$.
--
--   The one-dimensional integrals are what the certificate of Lemma 9.3 evaluates.
--
--   Differences from the source: none.
-- source:
--   Heilman, Sharp Hardness for MAX-3-CUT and Quantum MAX-CUT, arXiv:2608.00333 (held version, sha256 2b4f1d11…), Lemma 9.2, Eq. (118), p.33; standing assumption 0 < σ ≤ 1/2, p.32

import Mathlib
import Definitions.Def_HeilmanMax3Cut_ust
import Definitions.Def_HeilmanMax3Cut_u0
import Definitions.Def_HeilmanMax3Cut_B1
import Definitions.Def_HeilmanMax3Cut_Jst
import Definitions.Def_HeilmanMax3Cut_J0
import Definitions.Def_HeilmanMax3Cut_Fv

namespace HeilmanMax3Cut

/-- **Lemma 9.2.** Heilman, *Sharp Hardness for MAX-3-CUT and Quantum MAX-CUT*, arXiv:2608.00333 (held version,
sha256 2b4f1d11…), Lemma 9.2, Eq. (118), p.33, under the standing assumption `0 < σ ≤ 1/2`
(p.32): "`u_* = u₀ + 4B^{(1)}` by (108) and `J_* = J₀ + B^{(1)}` by (104) where
`u₀(t) := K₀1 = ½ ∫₀^{2/3} (2 + 3v) F_v(t) dv`, `J₀(t) = ½ ∫₀^{2/3} (3v − 1) F_v(t) dv`, `∀ t ≥ 0`."

**Formalization Note.** All four identities are stated at every `t ≥ 0`; the second holds by the
definition (104) of `J_*`. -/
theorem lemma_9_2 (σ : ℝ) (hσ : σ ∈ Set.Ioc (0 : ℝ) (1 / 2)) (t : ℝ) (ht : 0 ≤ t) :
    ust σ t = u0 σ t + 4 * B1 σ t ∧ Jst σ t = J0 σ t + B1 σ t ∧
    u0 σ t = 1 / 2 * ∫ v in (0 : ℝ)..(2 / 3), (2 + 3 * v) * Fv σ v t ∧
    J0 σ t = 1 / 2 * ∫ v in (0 : ℝ)..(2 / 3), (3 * v - 1) * Fv σ v t := by sorry

end HeilmanMax3Cut
