-- Prove2me | Theorems.Thm_FoundationsRL_GeneralDM_localized_offset_dec_lower_bound
-- name    : FoundationsRL.GeneralDM.localized_offset_dec_lower_bound
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-19T20:26:20.460008+00:00
-- url     : https://prove2.me/theorems/3687dea9-a8c8-4e5c-b495-7ad9e97ce03a
-- title:
--   Corollary 1 — localized offset-DEC lower bound (Eq. 6.32)
-- statement:
--   This theorem formalizes **Corollary 1** (Foster & Rakhlin, *Foundations of Reinforcement
--   Learning and Interactive Decision Making*, arXiv:2312.16730v1, p. 105, Eq. (6.32)), obtained
--   by combining Proposition 28 (the goal of this mission) with Proposition 27 (which relates the
--   constrained and offset DEC via localization): for every model class $\mathcal{M}$, horizon $T
--   \ge 1$, and algorithm — represented by any sequence $p : \mathrm{Fin}\,T \to (S \to
--   \mathbb{R})$ of decision distributions — there exists a model $m \in \mathcal{M}$ for which
--   $$
--   \mathbb{E}[\mathrm{Reg}(T)] \gtrsim \sup_{\gamma \gtrsim \sqrt{T}} \sup_{\hat m \in
--     \mathrm{co}(\mathcal{M})} \mathrm{dec}_\gamma\bigl(\mathcal{M}_{\alpha(T,\gamma)}(\hat m), \hat m\bigr),
--   $$
--   where $\alpha(T, \gamma) := c \cdot \gamma / T$ for an absolute constant $c > 0$. This
--   restates the lower bound in terms of the localized offset DEC, showing the lower bound's
--   reach beyond the constrained DEC of Proposition 28 itself.
--
--   **Formalization Note** As in Proposition 28, the absolute constants $c$ (inside
--   $\alpha(T,\gamma)$) and the overall $\gtrsim$ prefactor $C$ are existentially quantified
--   rather than pinned to specific numerals: the book states this corollary itself with $\gtrsim$
--   and does not work out either constant explicitly (unlike Proposition 28's own $1/20$, which
--   its proof derives in closed form). "Any algorithm" and $\mathrm{regret}$ are formalized
--   exactly as in Proposition 28: a fixed realized decision-distribution sequence $p$, not an
--   expectation over an adaptive algorithm's randomness. Unlike Proposition 28, this corollary
--   carries no localization hypothesis, so an explicit $\mathcal{M} \ne \emptyset$ hypothesis is
--   added (matching the book's own standing realizability assumption $M^\star \in \mathcal{M}$,
--   which makes $\mathcal{M}$ nonempty throughout the chapter) to keep the conclusion
--   satisfiable.
-- source:
--   Foster & Rakhlin, Foundations of Reinforcement Learning and Interactive Decision Making, arXiv:2312.16730v1, p. 106, Corollary 1, Eq. (6.32)

import Mathlib
import Definitions.Def_FoundationsRL_GeneralDM_Protocol
import Definitions.Def_FoundationsRL_GeneralDM_Divergences
import Definitions.Def_FoundationsRL_GeneralDM_DEC
import Definitions.Def_FoundationsRL_GeneralDM_LocalizedSubclass

namespace FoundationsRL.GeneralDM

/-- Corollary 1 (Foster & Rakhlin, *Foundations of Reinforcement Learning and Interactive Decision
Making*, arXiv:2312.16730v1, p. 105, Eq. (6.32)): combining Proposition 28 with Proposition 27,
for every model class `𝓜`, horizon `T ≥ 1`, and algorithm — represented by any sequence
`p : Fin T → S → ℝ` of decision distributions — there exists a model `m ∈ 𝓜` for which

`regret(f^m, π_m, T, p) ≥ C · sup_{γ ≳ √T} sup_{M̂ ∈ co(M)} decγ(Mα(T,γ)(M̂), M̂) · T`,

where `α(T, γ) := c · γ / T` for an absolute constant `c > 0`, and `C > 0` is the absolute constant
this corollary's derivation (combining Propositions 27 and 28) produces.

**Formalization Note** As in Proposition 28 above, the absolute constants `c` (inside `α(T, γ)`)
and `C` (the overall `≳` prefactor) are existentially quantified rather than pinned to specific
numerals: the book states this corollary itself with `≳` and does not work out either constant
explicitly, unlike Proposition 28's own `1/20`, which its proof derives in closed form. "Any
algorithm" and `regret` are formalized exactly as in Proposition 28: a fixed realized
decision-distribution sequence `p`, not an expectation over an adaptive algorithm's randomness.
As in Proposition 28, `∃ c C` is placed **before** the universally quantified `S`, `Y`, `𝓜`,
`rew`, `piStar`, `T`, `p`, so both constants are absolute — good for every model class and
horizon — rather than allowed to depend on them (the "universal constant placement" convention
used throughout this series). `hne : 𝓜.Nonempty` is added because, unlike the goal theorem, this
corollary carries no localization hypothesis to fail first: without it, the conclusion `∃ m ∈ 𝓜`
would be unsatisfiable at `𝓜 = ∅`. This matches the book's own standing realizability assumption
(Assumption 8, p. 94: the true model `M⋆` lies in `𝓜`), which makes `𝓜` nonempty throughout
Chapter 6, not an extra restriction. -/
theorem localized_offset_dec_lower_bound :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ {S Y : Type*} [Fintype S] [Fintype Y] (𝓜 : Set (S → Y → ℝ)) (rew : Y → ℝ)
        (piStar : (S → Y → ℝ) → S), (∀ m, ∀ π, fM rew m π ≤ fM rew m (piStar m)) →
        𝓜.Nonempty →
        ∀ (T : ℕ), 0 < T →
        ∀ (p : Fin T → S → ℝ), (∀ t, (∀ π, 0 ≤ p t π) ∧ ∑ π, p t π = 1) →
        ∃ m ∈ 𝓜, C *
          (sSup ((fun γ : ℝ =>
              sSup ((fun mhat : S → Y → ℝ =>
                  dec (localizedSubclass 𝓜 rew piStar mhat (c * γ / T)) rew piStar γ) ''
                convexHull ℝ 𝓜))
            '' {γ : ℝ | c * Real.sqrt T ≤ γ})) * T ≤
          regret (fM rew m) (piStar m) T p := by sorry

end FoundationsRL.GeneralDM
