-- Prove2me | Theorems.Thm_InfluencerAuth_Switch_lemma_1_corrected
-- name    : InfluencerAuth.Switch.lemma_1_corrected
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T04:13:37.251401+00:00
-- url     : https://prove2.me/theorems/4910a628-5e73-4d8c-a240-e9c5b9bc528f
-- title:
--   Lemma 1, p. 6 (corrected) — V(A + ε) − V(A) < γφε/r for A > 1/2
-- statement:
--   Let $0<\gamma<1$, $\varphi>1$ with $\gamma\varphi>1$, $\beta>0$ and $r>0$, and let $V$ be the influencer's value function. For every awareness level $A>\tfrac12$ and every $\varepsilon>0$ with $A+\varepsilon<1$,
--   $$
--   V(A+\varepsilon)-V(A)<\frac{\gamma\varphi\,\varepsilon}{r}.
--   $$
--   Once more than half of the potential followers are aware, a head start of $\varepsilon$ in awareness shrinks over time, so it is worth at most the discounted inauthentic profit on $\varepsilon$ extra followers forever. This bound feeds Lemma 2.
--
--   **Formalization Note** The printed Lemma 1 has the bound $\varepsilon/r$ and is false when $\gamma\varphi>1$: with $\gamma=\tfrac12$, $\varphi=4$, $r=1$, $\beta=\tfrac1{100}$, $A=0.6$, $\varepsilon=0.1$, always being inauthentic from $0.7$ earns at least $1.4$ while every policy from $0.6$ earns at most about $1.208$, so the difference exceeds $0.19>\varepsilon/r$. The paper's own argument bounds the profit gain per unit of extra awareness by $\max(1,\gamma\varphi)=\gamma\varphi$, which gives the corrected constant stated here. The restriction $A+\varepsilon<1$ keeps both values inside the awareness range of the model.
-- source:
--   Nistor, Selove, Villas-Boas, Management Science (Articles in Advance 2024), Lemma 1, p. 6 (corrected: ε/r replaced by γφε/r)

import Mathlib
import Definitions.Def_InfluencerAuth_Switch_Model
import Definitions.Def_InfluencerAuth_Switch_OptValue

namespace InfluencerAuth.Switch

/-- Lemma 1 (p. 6), corrected: the printed bound `ε / r` is replaced by `γ φ ε / r`
(the printed form is false; see the Formalization Note). -/
theorem lemma_1_corrected (γ φ β r : ℝ) (hγ0 : 0 < γ) (hγ1 : γ < 1) (hφ : 1 < φ)
    (hβ : 0 < β) (hr : 0 < r) (hγφ : 1 < γ * φ) (A ε : ℝ)
    (hA : 1 / 2 < A) (hε : 0 < ε) (hAε : A + ε < 1) :
    optValue β γ φ r (A + ε) - optValue β γ φ r A < γ * φ * ε / r := by sorry

end InfluencerAuth.Switch
