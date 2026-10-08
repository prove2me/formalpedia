-- Prove2me | Theorems.Thm_GilmoreGomoryTSP_Bottleneck_lemma_7_Gstar_connected
-- name    : GilmoreGomoryTSP.Bottleneck.lemma_7_Gstar_connected
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:25:08.064778+00:00
-- url     : https://prove2.me/theorems/5273e576-4007-48ac-8f14-1c73f515f118
-- title:
--   Lemma 7 — if ψ is a tour, G_ψ* is connected
-- statement:
--   Let $\varphi$ be a permutation of the jobs and let $\psi$ be a tour. Then the graph $G_\psi^*$ — all arcs $R_{q\varphi(q)}$ of $G_\varphi$ together with every arc $R_{q,q+1}$ for which (22a) $i\le q<\varphi^{-1}\psi(i)$ holds for some $i$ or (22b) $\varphi^{-1}\psi(j)\le q<j$ holds for some $j$ — is connected.
--
--   Consequently the added arcs of $G_\psi^*$ contain a spanning tree of $G_\varphi$; this is how a tour is compared with spanning trees of $G_\varphi$.
--
--   **Formalization Note** The ranking property of $\varphi$ is not used and not assumed; the statement is for an arbitrary permutation $\varphi$. A tour is a permutation with $\psi(s)\ne s$ for every nonempty proper subset $s$.
-- source:
--   Gilmore and Gomory, Sequencing a one state-variable machine, Oper. Res. 12 (1964), p. 668, Lemma 7

import Mathlib
import Definitions.Def_GilmoreGomoryTSP_Bottleneck_Model

namespace GilmoreGomoryTSP.Bottleneck

theorem lemma_7_Gstar_connected {n : ℕ} (φ ψ : Equiv.Perm (Fin (n + 1)))
    (hψ : GilmoreGomoryTSP.MinCost.IsTour ψ) : (Gstar φ ψ).Connected := by sorry

end GilmoreGomoryTSP.Bottleneck
