-- Prove2me | Theorems.Thm_IntervalMaxCutEPTAS_Scheme_lemma_4_1
-- name    : IntervalMaxCutEPTAS.Scheme.lemma_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:17:02.098992+00:00
-- url     : https://prove2.me/theorems/45145711-03d9-455c-9ac9-dc58db4fcb0d
-- title:
--   Lemma 4.1 — rank length versus degree
-- statement:
--   Let $\rho$ be a rank representation of a graph $G$ with $m$ edges, and $L_v=r_v-\ell_v$. Then every vertex satisfies $L_v\le 2\deg_G(v)+1$; if $L_v\ge 2$, then $\deg_G(v)\ge1$ and $L_v\le 3\deg_G(v)$; consequently
--
--   $$\sum_{v:\,L_v\ge2}L_v\le 6m.$$
--
--   This charges long intervals to edges, which bounds both the rejected degree (Lemma 4.2) and the rounding loss (Lemma 4.4).
--
--   Differences from the source:
--   - encoding: vertex set V(G) of size n → Fin n, with a rank representation ρ (fields l, r, injectivity, range 1..2n, l < r); reason: labelling the vertices 0..n−1 restricts no instance; the structure is exactly §4.1's representation
-- source:
--   Morteza Alimi, Hani Ahmadzadeh, STOC 2027 submission #636 (October 2026), Lemma 4.1, PDF p. 15 (printed p. 14)

import Mathlib
import Definitions.Def_IntervalMaxCutEPTAS_Scheme_Rank

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace IntervalMaxCutEPTAS.Scheme

/-- Lemma 4.1: `L_v ≤ 2 deg(v) + 1`; if `L_v ≥ 2` then `deg(v) ≥ 1` and `L_v ≤ 3 deg(v)`;
hence `Σ_{v : L_v ≥ 2} L_v ≤ 6m`. -/
theorem lemma_4_1 {n : ℕ} (ρ : RankRep n) :
    (∀ v, ρ.r v - ρ.l v ≤ 2 * ρ.graph.degree v + 1) ∧
    (∀ v, 2 ≤ ρ.r v - ρ.l v → 1 ≤ ρ.graph.degree v ∧ ρ.r v - ρ.l v ≤ 3 * ρ.graph.degree v) ∧
    ∑ v ∈ Finset.univ.filter (fun v => 2 ≤ ρ.r v - ρ.l v), (ρ.r v - ρ.l v) ≤
      6 * ρ.graph.edgeFinset.card := by sorry

end IntervalMaxCutEPTAS.Scheme
