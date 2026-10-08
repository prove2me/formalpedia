-- Prove2me | Theorems.Thm_HarmonicGames_Decomposition_lemma_4_5
-- name    : HarmonicGames.Decomposition.lemma_4_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T04:52:41.945485+00:00
-- url     : https://prove2.me/theorems/699b42ab-6671-4cee-9f13-276e3235611a
-- title:
--   Lemma 4.5 — normalized $\iff$ $\Pi_m u^m = u^m$ $\iff$ $\Pi u = u$ $\iff$ $u \in (\ker D)^\perp$
-- statement:
--   For a finite game with nonempty finite strategy sets and utilities $u = (u^m)_{m\in\mathcal M} \in C_0^{\mathcal M}$, recall that $u$ is **normalized** (Definition 4.1) if $\sum_{p^m\in E^m} u^m(p^m, p^{-m}) = 0$ for all $p^{-m}$ and all $m$.
--
--   **Lemma 4.5.** The following are equivalent:
--
--   1. $u$ is normalized;
--   2. $\Pi_m u^m = u^m$ for all $m$;
--   3. $\Pi u = u$;
--   4. $u \in (\ker D)^\perp$.
--
--   Normalized games are the representatives with the nonstrategic information removed; the lemma identifies them with the image of the projection $\Pi$.
--
--   **Formalization Note** The orthogonal complement in (4) is for the unweighted inner product $\sum_m\langle u^m,v^m\rangle_0$ on $C_0^{\mathcal M}$. The four conditions are stated with `List.TFAE`.
-- source:
--   Candogan, Menache, Ozdaglar, Parrilo, Flows and Decompositions of Games: Harmonic and Potential Games, arXiv:1005.2405v2, p. 16, Lemma 4.5 (with Definition 4.1, eq. (27))

import Mathlib
import Definitions.Def_HarmonicGames_Decomposition_Pinv
import Definitions.Def_HarmonicGames_Decomposition_Flows
import Definitions.Def_HarmonicGames_Decomposition_Games

namespace HarmonicGames.Decomposition

theorem lemma_4_5 (ι : Type) [Fintype ι] [DecidableEq ι] (E : ι → Type) [∀ m, Fintype (E m)]
    [∀ m, DecidableEq (E m)] [∀ m, Nonempty (E m)] (u : Games E) :
    List.TFAE [IsNormalized E u, ∀ m, Pim E m (u m) = u m, PiOp E u = u,
      u ∈ (LinearMap.ker (Dop E))ᗮ] := by sorry

end HarmonicGames.Decomposition
