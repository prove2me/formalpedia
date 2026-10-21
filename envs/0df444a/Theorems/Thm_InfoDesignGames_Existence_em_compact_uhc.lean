-- Prove2me | Theorems.Thm_InfoDesignGames_Existence_em_compact_uhc
-- name    : InfoDesignGames.Existence.em_compact_uhc
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:44:34.642739+00:00
-- url     : https://prove2.me/theorems/fad2e8c4-fd10-45ca-97cc-0d1b0f1f9124
-- title:
--   Proof of Theorem 1, p. 7 — compact convex upper hemicontinuous equilibrium correspondence
-- statement:
--   For every finite information design game $G_M$, the agents' equilibrium-outcome correspondence $E_M$ has compact convex values and is upper hemicontinuous:
--
--   $$\forall x,\quad E_M(x)\text{ is compact and convex},\qquad E_M:X\rightrightarrows\Delta(A)^M\text{ is upper hemicontinuous}.$$
--
--   Upper hemicontinuity means that whenever an open set contains every outcome in $E_M(x)$, it also contains every outcome in $E_M(x')$ for all $x'$ sufficiently near $x$. This is the continuation-game regularity used in Theorem 1.
--
--   **Formalization Note** The experiment and outcome spaces carry the finite-dimensional product topology and its Borel sigma algebra; compactness refers to that topology.
-- source:
--   Koessler, Laclau & Tomala, Interactive Information Design, SSRN working paper 3171992 (version of April 25, 2018), https://ssrn.com/abstract=3171992, p. 7, proof of Theorem 1

import Definitions.Def_InfoDesignGames_Existence_Model

namespace InfoDesignGames.Existence

theorem em_compact_uhc (G : Game) :
    (∀ x : Profile G, IsCompact (EM G x) ∧ Convex ℝ (EM G x)) ∧
      IsUHC (EM G) := by sorry

end InfoDesignGames.Existence
