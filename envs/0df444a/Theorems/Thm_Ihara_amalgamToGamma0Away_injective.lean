-- Prove2me | Theorems.Thm_Ihara_amalgamToGamma0Away_injective
-- name    : Ihara.amalgamToGamma0Away_injective
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.515241+00:00
-- url     : https://prove2.me/theorems/2b9dae2f-2781-56f4-87e8-2f8439cc90f0
-- title:
--   Injectivity of Ihara's amalgam homomorphism
-- statement:
--   Let $N$ and $q$ be natural numbers, let $q$ be prime and let $N$ be coprime to $q$. Consider the group [`Ihara.iharaAmalgam N q`](def/IharaAmalgam.html#L17), defined as the monoid pushout `Monoid.PushoutI (iharaEdge N q)` of the diagram `iharaEdge N q` of two homomorphisms out of a common edge group (the amalgam of the two vertex groups along that edge group), and the homomorphism [`Ihara.amalgamToAway N q`](def/IharaAmalgamMap.html#L87) obtained from this pushout by `iharaLift` applied to the two vertex homomorphisms `vertexZero N q` and `vertexOne N q` into $\mathrm{SL}(2, \mathtt{ZAway } q)$ together with their compatibility `vertex_compat N q` on the edge group. Its image lies in the subgroup `Gamma0Away N q` of $\mathrm{SL}(2, \mathtt{ZAway } q)$ consisting of those matrices $g$ for which the image of $N$ in `ZAway q` divides the entry $g_{1 0}$, and [`Ihara.amalgamToGamma0Away N q`](def/IharaAmalgamMap.html#L141) is the resulting corestricted homomorphism from the amalgam to `Gamma0Away N q`. The assertion is that this corestricted homomorphism is injective as a function.
--
--   This is the injectivity half of Ihara's theorem presenting $\Gamma_0(N)$ over $\mathbb{Z}[1/q]$ as an amalgam of two copies of $\Gamma_0(N)$ along $\Gamma_0(Nq)$, for a prime $q$ not dividing $N$. Combined with the corresponding surjectivity statement it yields the amalgam isomorphism, and it is used in the analysis of the level-raising kernel and of Hecke operators at $q$ through the factorisation results for homomorphisms out of `Gamma0Away N q`.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Ihara_amalgamToGamma0Away_injective.lean

import Definitions.Def_IharaAmalgamMap

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem Ihara.amalgamToGamma0Away_injective {N q : ℕ} (hq : q.Prime) (hqN : N.Coprime q) :
    Function.Injective (Ihara.amalgamToGamma0Away N q) := by sorry
