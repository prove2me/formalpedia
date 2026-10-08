-- Prove2me | Theorems.Thm_KelsoCrawford_OneSided_one_sided_market_has_strict_core
-- name    : KelsoCrawford.OneSided.one_sided_market_has_strict_core
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:34:25.907924+00:00
-- url     : https://prove2.me/theorems/09dd81b6-8493-4040-a4e9-ebc6b8620e6c
-- title:
--   Theorem 3 — a one-sided market satisfying gross substitutes has a strict core
-- statement:
--   Let $W$ be a finite set of workers and $v(C)$ the product obtainable by coalition $C\subseteq W$. Assume nonnegative marginal production (MP′), $v(C\cup\{i\})-v(C)\ge0$ for every $i,C$; no free lunch (NFL), $v(\varnothing)=0$; and gross substitutes (GS) when $v$ is used as the technology of each of $|W|+1$ identical fictitious firms, with arbitrary real salary vectors. Then there are a partition $P=(C_z)$ of $W$ and salaries $s_i$ in the one-sided strict core:
--
--   $$s_i\ge0\ (i\in W),\qquad \sum_{i\in W}s_i\le\sum_{C\in P}v(C),$$
--
--   and no coalition $C$ can offer $r_i\ge s_i$ to all of its members, with $r_i>s_i$ for at least one member, while paying $\sum_{i\in C}r_i\le v(C)$.
--
--   This is the existence claim of Theorem 3. The paper's worker utilities $\mu^i(s_i)$ are continuous and strictly increasing; they do not occur in D1′ or D2′ because these comparisons are equivalently written as salary comparisons.
--
--   **Formalization Note** Partitions have nonempty parts, salaries range over all real numbers, and GS is quantified over every pair of real salary vectors and every profit-maximizing worker set. The theorem admits empty worker sets; its conclusion remains the paper's empty-market case.
-- source:
--   Kelso and Crawford, Job matching, coalition formation, and gross substitutes, Econometrica 50 (1982), p. 1493, Theorem 3; D1′–D2′ on pp. 1492–1493

import Mathlib
import Definitions.Def_KelsoCrawford_OneSided_Model
import Definitions.Def_KelsoCrawford_OneSided_OneSided

namespace KelsoCrawford.OneSided

theorem one_sided_market_has_strict_core {W : Type} [Fintype W] [DecidableEq W]
    (v : Finset W → ℝ)
    (hMP : ∀ i (C : Finset W), 0 ≤ v (insert i C) - v C)
    (hNFL : v ∅ = 0)
    (hGS : GrossSubstitutesOn v Set.univ) :
    ∃ (P : Finpartition (Finset.univ : Finset W)) (s : W → ℝ),
      IsOneSidedStrictCore v P s := by sorry

end KelsoCrawford.OneSided
