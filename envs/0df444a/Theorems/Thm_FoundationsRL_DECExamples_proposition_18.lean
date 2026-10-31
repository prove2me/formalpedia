-- Prove2me | Theorems.Thm_FoundationsRL_DECExamples_proposition_18
-- name    : FoundationsRL.DECExamples.proposition_18
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:22:29.679001+00:00
-- url     : https://prove2.me/theorems/4f314f7a-1d36-4b6e-93f8-45d445197943
-- title:
--   Proposition 18 — DEC for Lipschitz bandits, $\mathrm{dec}_\gamma(\mathcal F,\widehat f)\lesssim\gamma^{-1/(d+1)}$
-- statement:
--   Let $(\Pi,\rho)$ be a nonempty metric space and $\mathcal F=\{f:\Pi\to[0,1]\mid f\text{ is }1\text{-Lipschitz w.r.t. }\rho\}$. Suppose there is $d>0$ with $\mathcal N_\rho(\Pi,\varepsilon)\le\varepsilon^{-d}$ for all $\varepsilon\in(0,1]$. Let $\widehat f:\Pi\to[0,1]$ and $\gamma\ge1$, and consider the strategy
--
--   1. let $\Pi'\subseteq\Pi$ witness the covering number $\mathcal N_\rho(\Pi,\varepsilon)$, with $\varepsilon=\gamma^{-1/(d+1)}$;
--   2. let $p$ be inverse gap weighting (3.36) with parameter $\gamma$ applied to $\widehat f$, restricted to the finite decision space $\Pi'$.
--
--   There is an absolute constant $C>0$ (independent of $\Pi$, $\rho$, $d$, $\widehat f$ and $\gamma$) such that this strategy certifies
--
--   $$
--   \sup_{f\in\mathcal F}\mathbb E_{\pi\sim p}\Big[f(\pi_f)-f(\pi)-\gamma\cdot\big(f(\pi)-\widehat f(\pi)\big)^2\Big]\le C\,\gamma^{-\frac{1}{d+1}},
--   \qquad\text{hence}\qquad
--   \mathrm{dec}_\gamma(\mathcal F,\widehat f)\le C\,\gamma^{-\frac{1}{d+1}}.
--   $$
--
--   Unlike the finite-dimensional examples, where the DEC decays like $\gamma^{-1}$, the Lipschitz class has a slower rate, and tuning $\gamma$ in the E2D bound gives regret of order $T^{(d+1)/(d+2)}$, which cannot be improved.
--
--   **Formalization Note** The certificate is stated for every cover witnessing $\mathcal N_\rho(\Pi,\varepsilon)$ and every inverse gap weighting distribution on it (both exist). The covering hypothesis is required on $(0,1]$, and $\varepsilon=\gamma^{-1/(d+1)}\le1$ because $\gamma\ge1$. The DEC is an infimum over countably supported distributions, computed in `EReal`.
--
--   Differences from the source:
--   - generalization: N_ρ(Π, ε) ≤ ε^{−d} for all ε > 0 → N_ρ(Π, ε) ≤ ε^{−d} for ε ∈ (0, 1]; reason: the printed hypothesis fails at every ε > 1 on a nonempty space (N_ρ ≥ 1 > ε^{−d}), so the printed proposition is vacuous; the Lean hypothesis is implied by the printed one, and the proof uses it only at ε = γ^{−1/(d+1)} ≤ 1
--   - reading: "by setting ε ∝ γ^{−1/(d+1)}, … ≲ γ^{−1/(d+1)}" → ε = γ^{−1/(d+1)} exactly, and an absolute constant C > 0 chosen before the space, d, f̂ and γ; reason: the proportionality constant is not given; the proof's balancing choice is constant 1, which yields ε + ε^{−d}/γ = 2γ^{−1/(d+1)}; a fixed choice is stronger than "for some choice"
--   - generalization: dec_γ(F, f̂) as a minimum over all distributions Δ(Π) → an infimum over countably supported distributions (PMF); reason: the infimum over a subset is at least the infimum over Δ(Π), so the Lean bound implies the source's; it avoids measurability of an arbitrary f̂
--   - encoding: f(π_f) → sup over Π of f; reason: π_f need not exist on a non-compact space; equal when it exists
--   - encoding: "this strategy certifies dec_γ(F, f̂) ≲ …" → two conjuncts, the certificate inequality of p. 69 for the explicit strategy and the bound on dec_γ(F, f̂); reason: the meaning of "certifies" given on p. 69
--   - encoding: a metric space Π → a nonempty metric space; reason: on the empty space Δ(Π) is empty and the DEC is undefined
--   - encoding: min and max in (4.15) → ⨅ and ⨆ in EReal; reason: neither need be attained on an infinite space; the explicit strategy of the first conjunct carries the attained bound
-- source:
--   Foster & Rakhlin, Foundations of Reinforcement Learning and Interactive Decision Making, arXiv:2312.16730v1, Proposition 18, pp. 73–74 (certification, p. 69)

import Mathlib
import Definitions.Def_FoundationsRL_DECExamples_decAt
import Definitions.Def_FoundationsRL_DECExamples_lipschitzClass
import Definitions.Def_FoundationsRL_DECExamples_HasCoveringGrowth
import Definitions.Def_FoundationsRL_DECExamples_IsCoverWitness
import Definitions.Def_FoundationsRL_DECExamples_IsIGWOn
open scoped NNReal

namespace FoundationsRL.DECExamples

/-- **Proposition 18 (DEC for Lipschitz Bandits).** Let `(D, ρ)` be a metric space with
`N_ρ(D, ε) ≤ ε^{−d}`, let `f̂ : D → [0, 1]` and `γ ≥ 1`, and let `F` be the `1`-Lipschitz functions
`D → [0, 1]`. With `ε = γ^{−1/(d+1)}`, inverse gap weighting on a cover witnessing `N_ρ(D, ε)`
certifies `dec_γ(F, f̂) ≲ γ^{−1/(d+1)}`.
Foster & Rakhlin, *Foundations of Reinforcement Learning and Interactive Decision Making*,
arXiv:2312.16730v1, Proposition 18, pp. 73–74.

**Formalization Note.** The two conjuncts are the certificate of p. 69 for the explicit strategy, and
the resulting bound on `dec_γ(F, f̂)`. `C` is absolute: it is chosen before the space, `d`, `f̂` and
`γ`. The covering hypothesis is on `ε ∈ (0, 1]`, see `HasCoveringGrowth`; `ε = γ^{−1/(d+1)}` lies in
that range because `γ ≥ 1`. `D` is nonempty, since `Δ(D)` is otherwise empty. -/
theorem proposition_18 :
    ∃ C : ℝ, 0 < C ∧ ∀ (D : Type*) [MetricSpace D] [Nonempty D] (d : ℝ), 0 < d →
      HasCoveringGrowth D d →
      ∀ fhat : D → ℝ, (∀ π, fhat π ∈ Set.Icc (0 : ℝ) 1) →
      ∀ γ : ℝ, 1 ≤ γ →
        (∀ (ε : ℝ≥0) (D' : Finset D) (p : PMF D), (ε : ℝ) = γ ^ (-1 / (d + 1)) →
          IsCoverWitness ε D' → IsIGWOn D' fhat γ p →
          ∀ f ∈ lipschitzClass D, offsetValue p f fhat γ ≤ C * γ ^ (-1 / (d + 1))) ∧
        decAt (lipschitzClass D) fhat γ ≤ ((C * γ ^ (-1 / (d + 1)) : ℝ) : EReal) := by sorry

end FoundationsRL.DECExamples
