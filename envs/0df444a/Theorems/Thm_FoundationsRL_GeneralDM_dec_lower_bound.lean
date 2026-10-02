-- Prove2me | Theorems.Thm_FoundationsRL_GeneralDM_dec_lower_bound
-- name    : FoundationsRL.GeneralDM.dec_lower_bound
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-19T20:25:39.575981+00:00
-- url     : https://prove2.me/theorems/d1769626-b381-4603-82dd-2561a3d15337
-- title:
--   Proposition 28 — DEC Lower Bound (Eq. 6.31)
-- statement:
--   This theorem formalizes **Proposition 28 (DEC Lower Bound [43])** (Foster & Rakhlin,
--   *Foundations of Reinforcement Learning and Interactive Decision Making*, arXiv:2312.16730v1,
--   p. 105, Eq. (6.31)) — the chapter's matching lower bound to Proposition 26's upper bound, and
--   unlike almost every other goal in this series, it does not name a specific algorithm: it
--   quantifies over **all** algorithms.
--
--   There are sufficiently small absolute constants $c, c' > 0$ such that, setting
--   $\varepsilon_T := c / \sqrt{T}$, for every model class $\mathcal{M}$, every horizon $T$
--   satisfying the **localization condition** $\mathrm{dec}^c_{\varepsilon_T}(\mathcal{M}) \ge
--   10\,\varepsilon_T$ (Eq. (6.30)), and every algorithm, there exists a model $m \in \mathcal{M}$
--   for which
--   $$
--   \mathbb{E}[\mathrm{Reg}(T)] \gtrsim \mathrm{dec}^c_{\varepsilon_T}(\mathcal{M}) \cdot T.
--   $$
--   Here "every algorithm" is represented by any sequence $p : \mathrm{Fin}\,T \to (S \to
--   \mathbb{R})$ of decision distributions, and the conclusion is
--   $$
--   c' \cdot \mathrm{dec}^c_{\varepsilon_T}(\mathcal{M}) \cdot T \le \mathrm{regret}(f^m, \pi_m, T, p).
--   $$
--
--   **Formalization Note** Three deliberate deviations from this series' usual "explicit
--   constants" rule, the first two flagged by the chapter brief and the third added at moderation
--   (round 2, `MODERATION.md`/`CHANGES_REQUESTED.md`, 2026-09-19). (i) The numerical constant $c$
--   in $\varepsilon_T := c/\sqrt{T}$ is explicitly called "not important" by the authors
--   (footnote a, p. 105), so it is existentially quantified — $\exists\, c > 0$ sufficiently
--   small — rather than pinned to a specific numeral. (ii) "Any algorithm" is formalized, as
--   throughout this series, without an explicit stochastic-process/history model: `regret` here
--   is the deterministic quantity of `FoundationsRL.GeneralDM.Protocol` evaluated at a fixed
--   realized decision-distribution sequence $p$, matching how $\mathrm{Reg}$ is already treated
--   deterministically in Proposition 26 above (the book's $\mathbb{E}[\mathrm{Reg}(T)]$ becomes
--   $\mathrm{regret}(\dots, p)$ for the realized $p$), rather than an expectation over an adaptive
--   algorithm's own randomness and a history-dependent strategy. (iii) The multiplicative constant
--   is *also* existentially quantified ($\exists\, c' > 0$) rather than pinned to $1/20$ as an
--   earlier draft of this item stated. The book's printed proof (§6.5.3, pp. 107–110) derives
--   $1/20$ only under two named simplifying assumptions it does not carry into this theorem's
--   hypotheses (p. 107, "Simplifications": a class-wide bounded-curvature hypothesis, Eq. (6.34);
--   and a bound on the *unaugmented* $\sup_{\hat M \in \mathcal M} \mathrm{decc}_\varepsilon(M,
--   \hat M)$ rather than the officially-defined, augmented $\mathrm{decc}_\varepsilon(M) =
--   \sup_{\hat M \in \mathrm{co}(\mathcal M)} \mathrm{decc}_\varepsilon(M \cup \{\hat M\}, \hat M)$
--   that $\mathrm{dec}^c_\varepsilon$ implements here). Since augmenting the inner sup's domain
--   from $\mathcal M$ to $\mathcal M \cup \{\hat M\}$ and the outer sup's domain from $\mathcal M$
--   to $\mathrm{co}(\mathcal M)$ can only raise the value, $\sup_{\hat M\in\mathcal M}
--   \mathrm{decc}_\varepsilon(M,\hat M) \le \mathrm{dec}^c_\varepsilon(\mathcal M)$ in general, so
--   the printed derivation of $\Delta/20$ (**p. 110**, Eq. (6.38): $\Delta :=
--   \mathrm{decc}_\varepsilon(M,\hat M)$ for the unaugmented, arbitrary $\hat M \in \mathcal M$)
--   does not license a pinned $1/20$ against the fully general, officially-defined
--   $\mathrm{dec}^c_\varepsilon$ this theorem's hypotheses and conclusion actually use. The book
--   itself states that the proof of the general statement (Proposition 28 as printed, with
--   neither restriction) is external (Foster, Golowich, Qian, Rakhlin & Sekhari 2023, "[43]"), not
--   in this document (arXiv:2312.16730v1); the existential $c'$ therefore matches the book's own
--   unpinned $\gtrsim$ for Proposition 28 as printed on pp. 105–106, rather than asserting a
--   numeral this citation basis does not establish. The model class $\mathcal{M}$ in the
--   localization condition and in the conclusion is kept as the same shared object throughout,
--   per the chapter brief's pitfall about not splitting it into two different quantifiers.
-- source:
--   Foster & Rakhlin, Foundations of Reinforcement Learning and Interactive Decision Making, arXiv:2312.16730v1, p. 105, Proposition 28, Eq. (6.31)

import Mathlib
import Definitions.Def_FoundationsRL_GeneralDM_Protocol
import Definitions.Def_FoundationsRL_GeneralDM_Divergences
import Definitions.Def_FoundationsRL_GeneralDM_ConstrainedDEC

namespace FoundationsRL.GeneralDM

/-- Proposition 28 (DEC Lower Bound [43]) (Foster & Rakhlin, *Foundations of Reinforcement
Learning and Interactive Decision Making*, arXiv:2312.16730v1, p. 105, Eq. (6.31)): there is a
sufficiently small absolute constant `c > 0` such that, setting `εT := c / √T`, for every model
class `𝓜`, every horizon `T` satisfying the localization condition `decc_{εT}(M) ≥ 10 εT`
(Eq. (6.30)), and every algorithm — represented by any sequence `p : Fin T → S → ℝ` of decision
distributions — there exists a model `m ∈ 𝓜` for which

`regret(f^m, π_m, T, p) ≳ decc_{εT}(M) · T`.

**Formalization Note** Three deliberate deviations from Rule 7 (explicit constants), the first
two flagged by the chapter brief, the third added at moderation (round 2, `MODERATION.md`,
`CHANGES_REQUESTED.md`): (i) the numerical constant `c` in `εT := c/√T` is explicitly called "not
important" by the authors (footnote a, p. 105), so it is existentially quantified — `∃ c > 0`
sufficiently small — rather than pinned to a specific numeral; (ii) "any algorithm" is formalized,
as throughout this series, without an explicit stochastic-process/history model: `regret` here is
the deterministic quantity of `Def_FoundationsRL_GeneralDM_Protocol` evaluated at a fixed realized
decision-distribution sequence `p`, matching how `Reg` is already treated deterministically in
Proposition 26 above (the book's `E[Reg(T)]` becomes `regret(…, p)` for the realized `p`), rather
than an expectation over the algorithm's own randomness and an adaptive history-dependent
strategy; (iii) the multiplicative constant is *also* existentially quantified (`∃ c' > 0`)
rather than pinned to `1/20`. The book's printed proof (§6.5.3, pp. 107–110) derives `1/20` only
under two named simplifying assumptions it does not carry into this theorem's hypotheses
(p. 107, "Simplifications": a class-wide bounded-curvature hypothesis, Eq. (6.34); and a bound on
the *unaugmented* `sup_{M̂∈𝓜} decc_ε(M,M̂)` rather than the officially-defined, augmented
`decc_ε(M) = sup_{M̂∈co(M)} decc_ε(M∪{M̂},M̂)` that `decC` implements here). Since augmenting the
inner sup's domain from `M` to `M∪{M̂}` and the outer sup's domain from `M` to `co(M)` can only
raise the value, `sup_{M̂∈𝓜} decc_ε(M,M̂) ≤ decC 𝓜 ⋯ ε` in general, so the printed derivation of
`Δ/20` (p. 110, Eq. (6.38): `Δ := decc_ε(M,M̂)` for the unaugmented, arbitrary `M̂ ∈ 𝓜`) does not
license a pinned `1/20` against the fully general, officially-defined `decC` this theorem's
hypotheses and conclusion actually use. The book itself states that the proof of the general
statement (Proposition 28 as printed, with no restriction to Eq. (6.34) and no restriction to the
unaugmented `sup`) is external (Foster, Golowich, Qian, Rakhlin & Sekhari 2023, "[43]"), not in
this document (arXiv:2312.16730v1); the existential `c'` therefore matches the book's own
unpinned `≳` for Proposition 28 as printed on pp. 105–106, before the "Simplifications"
restriction, rather than asserting a numeral this citation basis does not establish. `M` in the
localization condition and the model class of the conclusion are kept as the same shared `𝓜`
throughout, per the chapter brief's pitfall about not splitting them into two objects. Both
existentials `∃ c` and `∃ c'` are placed **before** the universally quantified `S`, `Y`, `𝓜`,
`rew`, `piStar`, `T`, `p` — matching the "universal constant placement" convention used
throughout this series (each is one absolute constant good for every model class and horizon, not
one that may depend on them). -/
theorem dec_lower_bound :
    ∃ c : ℝ, 0 < c ∧ ∃ c' : ℝ, 0 < c' ∧
      ∀ {S Y : Type*} [Fintype S] [Fintype Y] (𝓜 : Set (S → Y → ℝ)) (rew : Y → ℝ)
      (piStar : (S → Y → ℝ) → S), (∀ m, ∀ π, fM rew m π ≤ fM rew m (piStar m)) →
      ∀ T : ℕ, 0 < T →
      decC 𝓜 rew piStar (c / Real.sqrt T) ≥ 10 * (c / Real.sqrt T) →
      ∀ p : Fin T → S → ℝ, (∀ t, (∀ π, 0 ≤ p t π) ∧ ∑ π, p t π = 1) →
      ∃ m ∈ 𝓜, c' * decC 𝓜 rew piStar (c / Real.sqrt T) * T ≤
        regret (fM rew m) (piStar m) T p := by sorry

end FoundationsRL.GeneralDM
