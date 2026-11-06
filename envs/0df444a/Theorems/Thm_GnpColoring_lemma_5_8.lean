-- Prove2me | Theorems.Thm_GnpColoring_lemma_5_8
-- name    : GnpColoring.lemma_5_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T02:33:37.403711+00:00
-- url     : https://prove2.me/theorems/cfa58f36-4c57-4bbb-aaac-b46cd3bb1198
-- title:
--   Lemma 5.8 — connected hub sets and degree sums
-- statement:
--   There are absolute constants $c_3,c_4>0$ such that for fixed $0<\eta<1/2$ and sufficiently large fixed $d$, with probability $1-o(1)$ over $G\sim G(n,d/n)$, every nonempty connected vertex set $U$ with $G[U]$ a tree or unicyclic satisfies:
--
--   1. if $|U\cap H|\ge|U|/2$ then $|U|\le c_3\log n/d^{2\eta}$;
--   2. $\sum_{u\in U}\deg_G(u)\le c_4(d|U|+\log n)$.
--
--   Here $H$ is the set of hubs (degree $>d+d^{1/2+\eta}$).
--
--   Differences from the source:
--   - encoding: $G\sim G(n,d/n)$, "with probability $1-o(1)$" → probability under the Erdős–Rényi law with edge probability $d/n$ clamped into $[0,1]$ tends to $1$ as $n\to\infty$; reason: the clamp only affects $n<d$, which the limit never sees
-- source:
--   Schiller, Sampling Colorings on G(n, d/n) via Glauber Dynamics, STOC 2027 submission (manuscript sha256 da44ff7b…), Lemma 5.8, p.52

import Mathlib
import Definitions.Def_GnpColoring_IsTreeOrUnicyclic
import Definitions.Def_GnpColoring_hubs
import Definitions.Def_LPCommunity_SBMRecovery_Setting

open scoped Classical
open Finset
open Filter Topology

namespace GnpColoring

/-- **Lemma 5.8 (connected hub sets and degree sums).** There are absolute constants `c₃, c₄ > 0`
such that for fixed `0 < η < 1/2` and sufficiently large fixed `d`, with probability `1 − o(1)` over
`G ∼ G(n, d/n)`, every nonempty connected vertex set `U` for which `G[U]` is a tree or unicyclic
satisfies: (i) if `|U ∩ H| ≥ |U|/2` then `|U| ≤ c₃ log n / d^(2η)`; (ii) `Σ_{u∈U} deg_G(u) ≤ c₄(d|U| + log n)`.

Schiller, *Sampling Colorings on G(n, d/n) via Glauber Dynamics*, STOC 2027 submission manuscript (sha256 da44ff7b…), Lemma 5.8, p.52.

**Formalization Note** `H` is the set of hubs (`deg_G > Δ̄`, `Δ̄ = d + d^(1/2+η)`). Nonemptiness and
connectivity are part of `IsTreeOrUnicyclic` (connectedness of `G[U]`). -/
theorem lemma_5_8 :
    ∃ c₃ c₄ : ℝ, 0 < c₃ ∧ 0 < c₄ ∧ ∀ η : ℝ, 0 < η → η < 1 / 2 →
    ∃ d₀ : ℝ, ∀ d : ℝ, d₀ ≤ d →
      Tendsto (fun n : ℕ => LPCommunity.SBMRecovery.erProb n (d / n) (fun G =>
          ∀ U : Finset (Fin n), IsTreeOrUnicyclic G U →
            ((U.card : ℝ) ≤ 2 * ((U ∩ hubs G d η).card : ℝ) →
                (U.card : ℝ) ≤ c₃ * Real.log n / d ^ (2 * η)) ∧
            ∑ u ∈ U, (G.degree u : ℝ) ≤ c₄ * (d * U.card + Real.log n)))
        atTop (𝓝 1) := by sorry

end GnpColoring
