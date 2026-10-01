-- Prove2me | Theorems.Thm_LovaszSchrijver_Defect_tightGraph_not_colorable_two
-- name    : LovaszSchrijver.Defect.tightGraph_not_colorable_two
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T15:53:53.021503+00:00
-- url     : https://prove2.me/theorems/e4cfffd4-6216-4608-8924-3c54dc232201
-- title:
--   Lemma 2.11 — the graph of edges tight at every FRAC-maximizer is nonbipartite
-- statement:
--   Let $G = (V,E)$ be a finite graph with no isolated nodes and let $a \in \mathbb R_+^V$ be a nonnegative weight vector. Assume that
--   $$\max\{a^{\mathsf T}x : x \in \mathrm{STAB}(G)\} < \max\{a^{\mathsf T}x : x \in \mathrm{FRAC}(G)\}.$$
--   Let $E'$ be the set of those edges $ij$ of $G$ for which $y_i + y_j = 1$ holds for every vector $y \in \mathrm{FRAC}(G)$ maximizing $a^{\mathsf T}x$. Then the graph $(V, E')$ is nonbipartite, i.e. it is not 2-colourable.
--
--   This is the first step towards locating a node that is half-integral at every fractional optimum (Lemma 2.12), which drives the induction in Theorem 2.13.
--
--   **Formalization Note** The two maxima are given as numbers $s_S, s_F$ together with the hypotheses that they are the greatest elements of $\{a^{\mathsf T}x : x \in \mathrm{STAB}(G)\}$ and $\{a^{\mathsf T}x : x \in \mathrm{FRAC}(G)\}$; the assumption is $s_S < s_F$. "Nonbipartite" is `¬ (V, E').Colorable 2`.
-- source:
--   Lovász and Schrijver, Cones of matrices and set-functions and 0–1 optimization, SIAM J. Optim. 1(2) (1991), p. 181, Lemma 2.11

import Mathlib
import Definitions.Def_LovaszSchrijver_Defect_Index

namespace LovaszSchrijver.Defect

theorem tightGraph_not_colorable_two {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : ∀ v, ∃ w, G.Adj v w)
    (a : V → ℝ) (ha : ∀ i, 0 ≤ a i) (sS sF : ℝ)
    (hS : IsGreatest {s : ℝ | ∃ x ∈ STAB G, s = a ⬝ᵥ x} sS)
    (hF : IsGreatest {s : ℝ | ∃ x ∈ FRAC G, s = a ⬝ᵥ x} sF)
    (hlt : sS < sF) :
    ¬ (tightGraph G a).Colorable 2 := by sorry

end LovaszSchrijver.Defect
