-- Prove2me | Theorems.Thm_FracColorLocal_KrFree_corollary_4_2
-- name    : FracColorLocal.KrFree.corollary_4_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T07:13:27.211196+00:00
-- url     : https://prove2.me/theorems/b0a8711a-5b64-4085-ae22-4679608cc2f8
-- title:
--   Corollary 4.2 — sup U = sup Φ; a positive maximizer of Φ gives a positive global maximizer of U with U′_{u(v)}(w(v)) = 2w(N(v))
-- statement:
--   Let $G$ be a finite graph with no isolated vertices and $u>0$. Then
--
--   $$\sup_{w>0}U_{G,u}(w)=\sup_{s>0}\Phi_{G,u}(s).$$
--
--   If $\Phi_{G,u}$ attains its supremum at a positive vertex weight, then $U_{G,u}$ has a positive global maximizer $w$ (over positive weights); this $w$ also maximizes $U_{G,u}$ over nonnegative vertex weights and satisfies
--
--   $$U'_{u(v)}(w(v))=2w(N(v))\qquad(v\in V(G)). \tag{4.3}$$
--
--   It supplies the maximizer at which Corollary 5.5 bounds the triangle weight in the existence proof.
--
--   Differences from the source:
--   - encoding: $\sup_{w>0}$, $\sup_{s>0}$ → real `sSup` of the images of the positive weights; reason: both sets are nonempty and bounded above ($U\le\Phi\le\sum_vu(v)$), so `sSup` is the supremum.
--   - reading: "a positive global maximizer $w$" → a positive $w$ maximizing $U$ over all positive weights; reason: the next sentence adds maximality over nonnegative weights, which is also stated.
-- source:
--   Davies, Dhawan, Methuku, Nguyen, Seo, Fractional colorings of K_r-free graphs with local demands, arXiv:2611.04297 (PDF sha256 b3f2dcce…), p. 18 (PDF 19), Corollary 4.2, (4.3) (standing assumption u > 0 of §4, p. 16)

import Mathlib
import Definitions.Def_OAI_Combinatorics_CliqueFree_WeightedGraph
import Definitions.Def_FracColorLocal_KrFree_Potential

open OAI.CliqueFreeIndependence.WeightedGraph

namespace FracColorLocal.KrFree

/-- Corollary 4.2: `sup_{w>0} U = sup_{s>0} Φ`; a positive maximizer of `Φ` yields a positive
global maximizer `w` of `U`, which also maximizes `U` over nonnegative weights and satisfies
`U'_{u(v)}(w(v)) = 2 w(N(v))` (4.3). -/
theorem corollary_4_2 {V : Type*} [Fintype V] (G : SimpleGraph V) (u : V → ℝ)
    (hu : ∀ v, 0 < u v) (hiso : ∀ v, ∃ y, G.Adj v y) :
    sSup ((fun w => potential G u w) '' {w : V → ℝ | ∀ v, 0 < w v}) =
      sSup ((fun s => phiPot G u s) '' {s : V → ℝ | ∀ v, 0 < s v}) ∧
    ((∃ s : V → ℝ, (∀ v, 0 < s v) ∧ ∀ s' : V → ℝ, (∀ v, 0 < s' v) → phiPot G u s' ≤ phiPot G u s) →
      ∃ w : V → ℝ, (∀ v, 0 < w v) ∧
        (∀ w' : V → ℝ, (∀ v, 0 < w' v) → potential G u w' ≤ potential G u w) ∧
        (∀ w' : V → ℝ, (∀ v, 0 ≤ w' v) → potential G u w' ≤ potential G u w) ∧
        ∀ v, deriv (scalarU (u v)) (w v) = 2 * neighborMass G w v) := by sorry

end FracColorLocal.KrFree
