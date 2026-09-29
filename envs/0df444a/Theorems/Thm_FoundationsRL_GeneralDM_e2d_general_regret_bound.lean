-- Prove2me | Theorems.Thm_FoundationsRL_GeneralDM_e2d_general_regret_bound
-- name    : FoundationsRL.GeneralDM.e2d_general_regret_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-19T20:24:51.813021+00:00
-- url     : https://prove2.me/theorems/7f4cebdb-9a55-4f4e-b56b-26c03e358db0
-- title:
--   Proposition 26 — E2D regret bound for general decision making (Eq. 6.19)
-- statement:
--   This theorem formalizes **Proposition 26** (Foster et al. [40]) (Foster & Rakhlin,
--   *Foundations of Reinforcement Learning and Interactive Decision Making*, arXiv:2312.16730v1,
--   p. 101, Eq. (6.19)): running the Estimation-to-Decisions (E2D) meta-algorithm with exploration
--   parameter $\gamma > 0$ against a model class $\mathcal{M}$ guarantees
--   $$
--   \mathrm{Reg} \le \sup_{\hat m \in \hat{\mathcal{M}}} \mathrm{dec}_\gamma(\mathcal{M}, \hat m) \cdot T + \gamma \cdot \mathrm{EstH},
--   $$
--   where $\hat{\mathcal{M}}$ is any set containing every reference model $\hat m_t$ the online
--   estimation oracle produces, and $\mathrm{EstH} := \sum_{t=1}^T \mathbb{E}_{\pi_t \sim
--   p_t}[D_H^2(m^\star(\pi_t), \hat m_t(\pi_t))]$ is the cumulative Hellinger estimation error
--   (Eq. (6.18)). This is the chapter's own analogue of Proposition 13's E2D regret bound for
--   structured bandits, now for the general decision-making protocol and a general divergence
--   $D_H^2$ rather than squared-error estimation, giving the matching upper-bound pair to this
--   chapter's lower bound (Proposition 28).
--
--   The E2D property — that each realized $p_t$ achieves the value $\mathrm{decGf}(\mathcal{M},
--   \hat m_t)$ of the min-max game, i.e. is a minimizer over $\Delta(S)$ — is packaged as the
--   hypothesis `hE2D`: for every model $m \in \mathcal{M}$, the payoff of $p_t$ against $m$ is at
--   most that game value (which holds with equality at the true minimizer, but only $\le$ is
--   needed for the regret bound).
--
--   **Formalization Note** The book's qualifier "almost surely" refers to the randomness in the
--   observation process and the oracle's estimates $\hat m_t$; the inequality itself is a
--   deterministic consequence of the E2D minimization property for any realized run, so —
--   matching how earlier missions of this series package probability-$1-\delta$ guarantees as
--   explicit hypotheses on the realized run rather than full measure-theoretic statements — it is
--   stated here for a fixed realized sequence of $p$ and $\hat m$, with no explicit probability
--   space.
-- source:
--   Foster & Rakhlin, Foundations of Reinforcement Learning and Interactive Decision Making, arXiv:2312.16730v1, p. 101, Proposition 26, Eq. (6.19)

import Mathlib
import Definitions.Def_FoundationsRL_GeneralDM_Protocol
import Definitions.Def_FoundationsRL_GeneralDM_Divergences
import Definitions.Def_FoundationsRL_GeneralDM_DEC

namespace FoundationsRL.GeneralDM

/-- Proposition 26 (Foster et al. [40]) (Foster & Rakhlin, *Foundations of Reinforcement Learning
and Interactive Decision Making*, arXiv:2312.16730v1, p. 101, Eq. (6.19)): running the E2D
meta-algorithm with exploration parameter `γ > 0` against a model class `𝓜` guarantees

`Reg ≤ sup_{M̂ ∈ 𝓜̂} decγ(M, M̂) · T + γ · EstH`,

where `𝓜̂` is any set containing every reference model `M̂_t` the online estimation oracle produces,
and `EstH := Σ_t E_{π_t ∼ p_t}[D²_H(M⋆(π_t), M̂_t(π_t))]` is the cumulative Hellinger estimation
error (Eq. (6.18)). The E2D property — that each `p t` achieves the value `decGf 𝓜 rew piStar γ
(mhat t)` of the min-max game, i.e. is a minimizer over `Δ(S)` — is packaged as the hypothesis
`hE2D`: for every model `m ∈ 𝓜`, the payoff of `p t` against `m` is at most that game value (which
holds with equality at the true minimizer, but only `≤` is needed for the regret bound).

**Formalization Note** The book's qualifier "almost surely" refers to the randomness in the
observation process and the oracle's estimates `M̂_t`; the inequality itself is a deterministic
consequence of the E2D minimization property for any realized run, so — matching how earlier
missions of this series package probability-`1 − δ` guarantees as explicit hypotheses on the
realized run rather than full measure-theoretic statements — it is stated here for a fixed
realized sequence `p`, `mhat`, with no explicit probability space. -/
theorem e2d_general_regret_bound {S Y : Type*} [Fintype S] [Fintype Y]
    (𝓜 : Set (S → Y → ℝ)) (rew : Y → ℝ) (piStar : (S → Y → ℝ) → S)
    (hpiStar : ∀ m, ∀ π, fM rew m π ≤ fM rew m (piStar m))
    (γ : ℝ) (hγ : 0 < γ)
    (mstar : S → Y → ℝ) (hmstar : mstar ∈ 𝓜)
    (T : ℕ) (p : Fin T → S → ℝ) (hp : ∀ t, (∀ π, 0 ≤ p t π) ∧ ∑ π, p t π = 1)
    (mhat : Fin T → S → Y → ℝ) (hatM : Set (S → Y → ℝ)) (hhatM : ∀ t, mhat t ∈ hatM)
    (hE2D : ∀ t, ∀ m ∈ 𝓜, ∑ π, p t π *
        (fM rew m (piStar m) - fM rew m π - γ * hellingerSq (m π) (mhat t π)) ≤
      decGf 𝓜 rew piStar γ (mhat t)) :
    regret (fM rew mstar) (piStar mstar) T p ≤
      (sSup ((decGf 𝓜 rew piStar γ) '' hatM)) * T +
      γ * ∑ t : Fin T, ∑ π, p t π * hellingerSq (mstar π) (mhat t π) := by sorry

end FoundationsRL.GeneralDM
