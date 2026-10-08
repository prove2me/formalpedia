-- Prove2me | Theorems.Thm_FoundationsRL_GeneralDM_e2d_general_regret_bound_v2
-- name    : FoundationsRL.GeneralDM.e2d_general_regret_bound_v2
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-10-06T06:19:22.705994+00:00
-- url     : https://prove2.me/theorems/3fe36c5e-0526-4849-b82e-cc40433d562d
-- title:
--   Proposition 26 — E2D regret bound for general decision making, Eq. (6.19) (v2: models are probability kernels)
-- statement:
--   This is **Proposition 26** (Foster et al. [40]) of Foster & Rakhlin (arXiv:2312.16730v1, p. 101, Eq. (6.19)), the regret bound for the Estimation-to-Decisions (E2D) meta-algorithm in the general Decision Making with Structured Observations protocol.
--
--   **Setting (§6.1).** $\Pi$ is a finite decision space and $Y$ a finite alphabet of joint reward/observation outcomes, with $\mathrm{rew}:Y\to\mathbb R$ reading off the reward. Under Assumption 7 a model is a probability kernel $M:\Pi\to\Delta(Y)$, with mean reward $f^M(\pi)=\sum_y M(\pi)(y)\,\mathrm{rew}(y)$ and optimal decision $\pi_M\in\arg\max_\pi f^M(\pi)$ (a fixed selector). The class $\mathcal M$ consists of such models and contains the true model $M^\star$ (Assumption 8). The offset DEC at a reference model $\hat M$ is
--   $$\mathrm{dec}_\gamma(\mathcal M,\hat M)=\inf_{p\in\Delta(\Pi)}\sup_{M\in\mathcal M}\mathbb E_{\pi\sim p}\big[f^M(\pi_M)-f^M(\pi)-\gamma D^2_{\mathrm H}(M(\pi),\hat M(\pi))\big]$$
--   (Eq. (6.9)), $D^2_{\mathrm H}$ the squared Hellinger distance. E2D with exploration parameter $\gamma>0$ plays, at round $t$, a distribution $p_t$ attaining the infimum against the oracle's estimate $\hat M_t$ (Eq. (6.17)); this is packaged for the realized run as: for every $M\in\mathcal M$ the payoff of $p_t$ against $M$ is at most $\mathrm{dec}_\gamma(\mathcal M,\hat M_t)$.
--
--   **Proposition.** For any set $\hat{\mathcal M}$ of models containing every estimate $\hat M_t$,
--   $$\mathrm{Reg}=\sum_{t=1}^T\Big(f^{M^\star}(\pi_{M^\star})-\mathbb E_{\pi_t\sim p_t}f^{M^\star}(\pi_t)\Big)\le\sup_{\hat M\in\hat{\mathcal M}}\mathrm{dec}_\gamma(\mathcal M,\hat M)\cdot T+\gamma\cdot\mathrm{Est}_{\mathrm H},\qquad \mathrm{Est}_{\mathrm H}=\sum_{t=1}^T\mathbb E_{\pi_t\sim p_t}\big[D^2_{\mathrm H}(M^\star(\pi_t),\hat M_t(\pi_t))\big]$$
--   (Eqs. (6.18)–(6.19)).
--
--   **Formalization Note.** The retired version let the members of $\mathcal M$ and the estimates $\hat M_t$ be arbitrary real-valued kernels, so the DEC values over a legitimate $\hat{\mathcal M}$ could be unbounded and Lean's real `sSup` returned the junk value $0$, degrading the claim to $\mathrm{Reg}\le\gamma\,\mathrm{Est}_{\mathrm H}$ (the accepted disproof). The new statement writes Assumption 7 in: every $M\in\mathcal M$ and every $\hat M_t$ is a probability kernel ($M(\pi)\ge 0$, $\sum_yM(\pi)(y)=1$). With $Y$ finite this makes every mean reward lie between $\min\mathrm{rew}$ and $\max\mathrm{rew}$, hence $\mathrm{dec}_\gamma(\mathcal M,\hat M)\le\max\mathrm{rew}-\min\mathrm{rew}$ for every $\hat M$ and the supremum over $\hat{\mathcal M}$ is a genuine real supremum; the inner suprema and infimum of `decGf` are likewise honest (bounded, over nonempty sets) whenever $T\ge 1$. No bound on the reward range is assumed beyond finiteness of $Y$ (the section allows general $\mathcal R\subseteq\mathbb R$). Conventions kept from the retired version: the "almost surely" of the book refers to the realized run, so the inequality is stated for an arbitrary realized sequence $(p_t,\hat M_t)$ satisfying the E2D property; $\pi_M$ is a fixed argmax selector supplied for every kernel; rounds are $0$-indexed; for $T=0$ both sides are $0$.
-- source:
--   Foster & Rakhlin, Foundations of Reinforcement Learning and Interactive Decision Making, arXiv:2312.16730v1, p. 101, Proposition 26, Eqs. (6.17)–(6.19); Assumption 7 (p. 94), Eq. (6.9) (p. 97)

import Mathlib
import Definitions.Def_FoundationsRL_GeneralDM_Protocol
import Definitions.Def_FoundationsRL_GeneralDM_Divergences
import Definitions.Def_FoundationsRL_GeneralDM_DEC

namespace FoundationsRL.GeneralDM

/-- **Proposition 26** (Foster et al. [40]; Foster & Rakhlin, arXiv:2312.16730v1, p. 101,
Eq. (6.19)): in the DMSO protocol under Assumption 7 (every model `M : Π → Δ(ℛ × 𝒪)` is a
probability kernel; here `Y` is the finite joint reward/observation alphabet and
`rew : Y → ℝ` reads off the reward), running the E2D meta-algorithm with exploration
parameter `γ > 0` against a model class `𝓜 ∋ M⋆` guarantees
`Reg ≤ sup_{M̂ ∈ 𝓜̂} dec_γ(𝓜, M̂) · T + γ · Est_H`, where `𝓜̂` is any set containing every
estimate `M̂_t` of the online estimation oracle (each a model, i.e. a probability kernel) and
`Est_H = Σ_t E_{π_t ∼ p_t}[D²_H(M⋆(π_t), M̂_t(π_t))]` (Eq. (6.18)). The E2D property (6.17) is
packaged, for the realized run, as `hE2D`: against every `m ∈ 𝓜` the payoff of `p_t` is at most
the game value `dec_γ(𝓜, M̂_t)`.

Corrected replacement of `e2d_general_regret_bound`: the retired statement let the "models"
in `𝓜` and the `M̂_t` be arbitrary real-valued kernels, so the DEC image over `𝓜̂` could be
unbounded and Lean's real `sSup` returned the junk value `0`. With the models probability
kernels (Assumption 7) and `Y` finite, every mean reward `f^m(π)` lies between `min rew` and
`max rew`, `dec_γ(𝓜, M̂) ≤ max rew - min rew` for every `M̂`, and the supremum is honest. -/
theorem e2d_general_regret_bound_v2 {S Y : Type*} [Fintype S] [Fintype Y]
    (𝓜 : Set (S → Y → ℝ)) (rew : Y → ℝ) (piStar : (S → Y → ℝ) → S)
    (hpiStar : ∀ m, ∀ π, fM rew m π ≤ fM rew m (piStar m))
    (h𝓜 : ∀ m ∈ 𝓜, ∀ π, (∀ y, 0 ≤ m π y) ∧ ∑ y, m π y = 1)
    (γ : ℝ) (hγ : 0 < γ)
    (mstar : S → Y → ℝ) (hmstar : mstar ∈ 𝓜)
    (T : ℕ) (p : Fin T → S → ℝ) (hp : ∀ t, (∀ π, 0 ≤ p t π) ∧ ∑ π, p t π = 1)
    (mhat : Fin T → S → Y → ℝ)
    (hmhat : ∀ t, ∀ π, (∀ y, 0 ≤ mhat t π y) ∧ ∑ y, mhat t π y = 1)
    (hatM : Set (S → Y → ℝ)) (hhatM : ∀ t, mhat t ∈ hatM)
    (hE2D : ∀ t, ∀ m ∈ 𝓜, ∑ π, p t π *
        (fM rew m (piStar m) - fM rew m π - γ * hellingerSq (m π) (mhat t π)) ≤
      decGf 𝓜 rew piStar γ (mhat t)) :
    regret (fM rew mstar) (piStar mstar) T p ≤
      (sSup ((decGf 𝓜 rew piStar γ) '' hatM)) * T +
      γ * ∑ t : Fin T, ∑ π, p t π * hellingerSq (mstar π) (mhat t π) := by sorry

end FoundationsRL.GeneralDM
