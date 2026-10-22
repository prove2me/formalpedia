-- Prove2me | Theorems.Thm_GeomDL_WL_injective_phi_one_wl_step
-- name    : GeomDL.WL.injective_phi_one_wl_step
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-21T13:41:50.819161+00:00
-- url     : https://prove2.me/theorems/f521578f-7026-47ba-ae3a-e3e587a8480e
-- title:
--   §4.1, p. 34 — when φ is injective, the local layer is one step of the Weisfeiler–Lehman test
-- statement:
--   Let $\phi : F \times \mathrm{Multiset}(F) \to F$ be injective, that is, $\phi(x, S) = \phi(x', S')$ implies $x = x'$ and $S = S'$. Let $G$ and $G'$ be two graphs, $s \ge 0$ a round, and $h : V(G) \to F$, $h' : V(G') \to F$ node features that are an injective image of the round-$s$ Weisfeiler–Lehman colours $c^s$ across the two graphs: for all nodes $u$ of $G$ and $v$ of $G'$,
--   $$
--   h_u = h'_v \iff c^s_G(u) = c^s_{G'}(v).
--   $$
--   Then after one application of the local layer (13) the same holds one round later: for all $u$, $v$,
--   $$
--   \phi\big(h_u, \{\!\{h_w : w \in \mathcal N_u\}\!\}\big) = \phi\big(h'_v, \{\!\{h'_w : w \in \mathcal N_v\}\!\}\big) \iff c^{s+1}_G(u) = c^{s+1}_{G'}(v).
--   $$
--
--   This is the precise sense in which an injective local function performs one step of the Weisfeiler–Lehman colour refinement, where $c^{s+1}(u)$ is the pair of $c^s(u)$ and the multiset of the colours $c^s$ of the neighbours of $u$.
--
--   **Formalization Note** The book's sentence is informal; it is stated here as the one-step correspondence between equality of features and equality of WL colours. Colours are the history-carrying colours `neighborColor` of the reused definition `WLIdentification`, so they are comparable across graphs. Taking $G' = G$ gives the single-graph version.
-- source:
--   Bronstein et al., Geometric Deep Learning (arXiv:2104.13478v2), §4.1, p. 34, "When φ is injective, it is equivalent to one step of the Weisfeiler-Lehman graph isomorphism test"

import Mathlib
import Definitions.Def_WLIdentification
import Definitions.Def_GeomDL_WL_Defs

namespace GeomDL.WL
open OAI.WLIdentification

/-- §4.1, p. 34: when the local function `φ` of the layer (13) is injective (as a function of the
pair `(x_u, X_{N_u})`), one application of the layer is one step of the Weisfeiler–Lehman colour
refinement: if, across two graphs `G` and `G'`, equal round-`s` features are exactly equal
round-`s` WL colours, then equal features after the layer are exactly equal round-`(s+1)` colours. -/
theorem injective_phi_one_wl_step {F : Type*} (φ : F → Multiset F → F)
    (hφ : Function.Injective2 φ) (G G' : Graph) (s : ℕ)
    (h : Fin G.order → F) (h' : Fin G'.order → F)
    (hs : ∀ u v, h u = h' v ↔ neighborColor G s u = neighborColor G' s v) :
    ∀ u v, localLayer φ G h u = localLayer φ G' h' v ↔
      neighborColor G (s + 1) u = neighborColor G' (s + 1) v := by sorry

end GeomDL.WL
