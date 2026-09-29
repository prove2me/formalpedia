-- Prove2me | Theorems.Thm_KServer_tree_anchor_at_request
-- name    : KServer.tree_anchor_at_request
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-01T07:40:47.343663+00:00
-- url     : https://prove2.me/theorems/fd46dd8f-9d87-4701-9c00-32bd29f0125a
-- title:
--   The anchoring theorem: the CK potential minimum is attained at the request
-- statement:
--   Let $M$ be a finite tree vertex space of diameter at most $\Delta$, and let $\Phi_{x_1x_2x_3}(w) = w(x_1x_2x_3) + w(\bar x_1x_2x_3) + w(\bar x_2\bar x_2x_3) + w(\bar x_3\bar x_3\bar x_3)$ be the Coester--Koutsoupias potential of a $3$-server instance, evaluated on the unlabelled work function $w$ of the antipodal extension of $M$ after the request sequence $\sigma r$. Then the minimum of $\Phi$ over all anchor triples is attained at a triple whose **last anchor is the final request**:
--
--   $$\min_{y_1,y_2,y_3 \in M} \Phi_{y_1y_2y_3}(w) \;=\; \Phi_{yzr}(w) \qquad \text{for some } y, z \in M.$$
--
--   ## Role
--
--   This is the anchoring theorem — the combinatorial heart of Coester--Koutsoupias' Theorem 23 ('Towards the k-server conjecture', ICALP 2021) for $k = 3$, and the key input to the update property of the potential $\Phi = \min \Phi_{y_1y_2y_3}$ for the unlabelled work function algorithm on trees. Once the minimum is anchored at the request, the growth bound $w'(\bar r\bar r\bar r) \le w(\bar r \bar r\bar r)$ (extreme-cost maximization at the antipode) and monotonicity of the work function turn the per-request increase of $\Phi$ into the desired $-\,\mathrm{growth}$ bound, giving $3$-competitiveness via the potential criterion.
--
--   ## Proof structure
--
--   The proof is a complete dispatch over the resolution structure of the work function at a swap-symmetric minimising triple $(x_1, x_2, x_3)$ supplied by Lemma 25 (`tree_swap_first_two`):
--
--   1. If $(x_1x_2x_3)$ resolves in slot 1 or 2, or its companion $(\bar x_1x_2x_3)$ resolves in slot 1, the push case (`anchor_push_case`, CK Lemma 21) moves the resolved anchor to the end.
--   2. If both $(x_1x_2x_3)$ and $(\bar x_1x_2x_3)$ resolve in slot 3, the tree lemma (`anchor_L26_case`, via CK Lemma 26) replaces $x_3$ by $r$.
--   3. In the remaining deep case — $(x_1x_2x_3)$ resolves in slot 3, $(\bar x_1x_2x_3)$ in slot 2 — the swap symmetry of Lemma 25 forces $d(x_1,x_2) = d(r,x_1) + d(r,x_2)$ (the request lies between the first two anchors). If $(\bar x_2\bar x_2x_3)$ resolves through the antipodal server, quasiconvexity closes the case (`anchor_quasiconvex_case`); otherwise it resolves in slot 3 and a second quasiconvexity pairing, splitting $(\bar x_2 r) \times (x_1 x_3)$ over the common coordinate $\bar x_2$, combined with the dispatch of $(\bar x_2\bar x_2x_1)$ and Lipschitz equality-forcing, produces the slot-3 resolution of $(\bar x_2 x_1 x_3)$ needed to re-enter the Lemma 26 case on the swapped triple $(x_2, x_1, x_3)$.
--
--   Every branch lands on a triple of the form $(\cdot\,,\cdot\,,r)$ whose potential is at most the minimum, so equality holds by minimality.
--
--   ## Formalization note
--
--   Stated over `ckPot`/`ckPotAt` from the published `KServer_ck_potential` definitions; `IsTreeVertexSpace` is the four-point tree condition of the published tree metric definitions. The hypothesis list matches Lemma 25 exactly, so the two theorems compose directly.
-- source:
--   C. Coester, E. Koutsoupias, 'Towards the k-server conjecture', ICALP 2021, arXiv:2102.10474, Theorem 23 (case analysis assembled from Lemmas 21, 25, 26 and quasiconvexity), specialised to k = 3.

import Mathlib
import Definitions.Def_KServer_workfunctionU
import Definitions.Def_KServer_antipodal_extension
import Definitions.Def_KServer_tree_metric
import Definitions.Def_KServer_ck_potential

namespace KServer

theorem tree_anchor_at_request (M : Type) [MetricSpace M] [Fintype M] [Nonempty M]
    (hM : IsTreeVertexSpace M) (Δ : ℝ) (hΔ0 : 0 < Δ) (hΔ : ∀ u v : M, dist u v ≤ Δ)
    (C₀ : Config 3 M) (σ : List M) (r : M) :
    ∃ y z : M, ckPot M Δ hΔ0 hΔ C₀ (σ ++ [r]) = ckPotAt M Δ hΔ0 hΔ C₀ (σ ++ [r]) y z r := by sorry

end KServer
