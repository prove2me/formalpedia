-- Prove2me | Theorems.Thm_InfluencerAuth_Switch_lemma_2_corrected
-- name    : InfluencerAuth.Switch.lemma_2_corrected
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T04:12:34.098549+00:00
-- url     : https://prove2.me/theorems/0cca77ce-9220-47a5-bee8-a03d86086efc
-- title:
--   Lemma 2, p. 6 (corrected) — inauthentic once A > 1/2 and γφ − 1 > (γφ/r)(1 − γ)β(1 − A)
-- statement:
--   Let $0<\gamma<1$, $\varphi>1$ with $\gamma\varphi>1$, $\beta>0$ and $r>0$. If the current awareness $A_0\in(\tfrac12,1)$ satisfies
--   $$
--   \gamma\varphi-1>\frac{\gamma\varphi}{r}\,(1-\gamma)\,\beta\,(1-A_0),
--   $$
--   then always being inauthentic from $A_0$ on is an optimal policy: some admissible path of the policy $S=\mathbb R$ from $A_0$ is optimal from $A_0$.
--
--   The left side is the extra instantaneous profit per unit awareness from being inauthentic; the right side bounds the value of the faster awareness growth from being authentic. The lemma is the starting point of the backward induction of §3.3: once awareness is large enough, the influencer monetizes.
--
--   **Formalization Note** The printed Lemma 2 has the factor $1/r$ in place of $\gamma\varphi/r$ and is false: with $\gamma=\tfrac12$, $\varphi=4$, $\beta=4$, $r=1$, $A_t=0.51$ its hypothesis holds ($1>0.98$), yet the switching threshold of Proposition 1 is $A^*\approx0.537$, so the influencer is still authentic at $0.51$. The factor $\gamma\varphi/r$ is the one the corrected Lemma 1 supplies. "Inauthentic at time $t$" is read as "always being inauthentic is optimal from the current awareness"; the region of the hypothesis is forward invariant because awareness never decreases.
-- source:
--   Nistor, Selove, Villas-Boas, Management Science (Articles in Advance 2024), Lemma 2, p. 6 (corrected: 1/r replaced by γφ/r)

import Mathlib
import Definitions.Def_InfluencerAuth_Switch_Model

namespace InfluencerAuth.Switch

/-- Lemma 2 (p. 6), corrected: the printed factor `1/r` is replaced by `γ φ / r`
(the printed form is false; see the Formalization Note). -/
theorem lemma_2_corrected (γ φ β r : ℝ) (hγ0 : 0 < γ) (hγ1 : γ < 1) (hφ : 1 < φ)
    (hβ : 0 < β) (hr : 0 < r) (hγφ : 1 < γ * φ) (A₀ : ℝ)
    (hA₀ : A₀ ∈ Set.Ioo (1 / 2 : ℝ) 1)
    (hgain : γ * φ - 1 > γ * φ / r * (1 - γ) * β * (1 - A₀)) :
    ∃ A : ℝ → ℝ, IsOptimalFrom β γ φ r A₀ Set.univ A := by sorry

end InfluencerAuth.Switch
