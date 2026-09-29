-- Prove2me | Theorems.Thm_KServer_anchor_L26_case
-- name    : KServer.anchor_L26_case
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-01T07:19:21.284602+00:00
-- url     : https://prove2.me/theorems/d0c49bff-a36a-4ef9-81fd-97feef4f0aa3
-- title:
--   The Lemma-26 case of the anchoring theorem
-- statement:
--   Let $\Phi_{x_1x_2x_3}$ be the anchored Coester--Koutsoupias potential of a $3$-server instance ending with the request $r$, on (the antipodal extension of) a finite tree vertex space. Suppose the first two summands of the triple $(a, b, c)$ both **resolve in the third slot**:
--
--   $$w(abc) = w(abr) + d(r,c), \qquad w(\bar a b c) = w(\bar a b r) + d(r,c).$$
--
--   Then the last anchor may be replaced by the request outright:
--
--   $$\Phi_{abr}(w) \;\le\; \Phi_{abc}(w).$$
--
--   ## Role
--
--   This is the case of the Theorem 23 analysis in which the minimising triple and its antipodal companion both resolve through the third anchor. The two hypotheses convert the first two summands of $\Phi_{abc}$ into those of $\Phi_{abr}$ at a cost of $2\,d(r,c)$, and Lemma 26 --- the tree lemma $w(\bar b\,\bar b\,r) + w(\bar r^3) \le w(\bar b\,\bar b\,c) + w(\bar c^3) + 2\,d(r,c)$ --- absorbs exactly that cost in the last two summands. Applied to a minimising triple it directly exhibits the potential's minimum at a triple ending with the request, with no pushing needed. The tree enters only through Lemma 26.
-- source:
--   C. Coester, E. Koutsoupias, 'Towards the k-server conjecture', ICALP 2021, arXiv:2102.10474, proof of Theorem 23, the case 'If it resolves from x₃, then Φ(w) = … ≥ … = Φ_{x₁x₂r}(w), where the inequality is due to lem:treeResolveLastTwo'.

import Mathlib
import Definitions.Def_KServer_workfunctionU
import Definitions.Def_KServer_antipodal_extension
import Definitions.Def_KServer_ck_potential
import Definitions.Def_KServer_tree_metric

namespace KServer

theorem anchor_L26_case (M : Type) [MetricSpace M] [Fintype M] (hM : IsTreeVertexSpace M)
    (Δ : ℝ) (hΔ0 : 0 < Δ) (hΔ : ∀ u v : M, dist u v ≤ Δ)
    (C₀ : Config 3 M) (σ : List M) (r a b c : M)
    (h0 : @workFnU 3 (M ⊕ M) (antipodalExtension M Δ hΔ0 hΔ)
          (fun i => Sum.inl (C₀ i)) ((σ ++ [r]).map Sum.inl) ![Sum.inl a, Sum.inl b, Sum.inl c]
        = @workFnU 3 (M ⊕ M) (antipodalExtension M Δ hΔ0 hΔ)
          (fun i => Sum.inl (C₀ i)) ((σ ++ [r]).map Sum.inl) ![Sum.inl a, Sum.inl b, Sum.inl r]
          + dist r c)
    (h1 : @workFnU 3 (M ⊕ M) (antipodalExtension M Δ hΔ0 hΔ)
          (fun i => Sum.inl (C₀ i)) ((σ ++ [r]).map Sum.inl) ![Sum.inr a, Sum.inl b, Sum.inl c]
        = @workFnU 3 (M ⊕ M) (antipodalExtension M Δ hΔ0 hΔ)
          (fun i => Sum.inl (C₀ i)) ((σ ++ [r]).map Sum.inl) ![Sum.inr a, Sum.inl b, Sum.inl r]
          + dist r c) :
    ckPotAt M Δ hΔ0 hΔ C₀ (σ ++ [r]) a b r ≤ ckPotAt M Δ hΔ0 hΔ C₀ (σ ++ [r]) a b c := by sorry

end KServer
