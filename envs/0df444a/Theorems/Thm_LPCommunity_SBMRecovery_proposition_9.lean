-- Prove2me | Theorems.Thm_LPCommunity_SBMRecovery_proposition_9
-- name    : LPCommunity.SBMRecovery.proposition_9
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T11:04:59.603771+00:00
-- url     : https://prove2.me/theorems/ba5e42c9-bbd5-4935-9619-9efde7a6e8c8
-- title:
--   Proposition 9, p. 24 — κ(G) = d_min for G ∼ G_{n,p} w.h.p. (Bollobás–Thomason)
-- statement:
--   Fix $p\in(0,1)$ and let $G\sim\mathcal G_{n,p}$. Let $\kappa(G)$ be the node connectivity of $G$ and $d_{\min}$ its minimum degree. Then
--   $$
--   \mathbb P\big[\kappa(G)=d_{\min}\big]\longrightarrow 1\qquad(n\to\infty).
--   $$
--
--   One always has $\kappa(G)\le d_{\min}$ for non-complete graphs; the content is that the two coincide for dense random graphs (Bollobás–Thomason, Theorem 1). In the proof of Proposition 4 it bounds the number of components left after deleting few nodes.
--
--   **Formalization Note** $\kappa$ follows the paper's convention $\kappa(K_n)=n$; complete graphs have probability $p^{\binom n2}\to 0$, so the convention does not affect the limit.
-- source:
--   Del Pia, Khajavirad, Kunisky, Linear Programming and Community Detection, arXiv:2006.03213v2, p. 24, Proposition 9 (Theorem 1 of Bollobás–Thomason)

import Mathlib
import Definitions.Def_LPCommunity_SBMRecovery_Setting
import Definitions.Def_LPCommunity_SBMRecovery_Factors

open Finset Filter Topology
open scoped Classical

namespace LPCommunity.SBMRecovery

/-- Proposition 9 (p. 24; Bollobás–Thomason): for `G ∼ G_{n,p}` with `p ∈ (0,1)`, with high
probability `κ(G) = d_min`. -/
theorem proposition_9 (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
    Tendsto (fun n : ℕ => erProb n p (fun G => kappa G = dMin G)) atTop (𝓝 1) := by sorry

end LPCommunity.SBMRecovery
