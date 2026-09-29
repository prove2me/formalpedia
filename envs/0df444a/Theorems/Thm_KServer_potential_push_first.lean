-- Prove2me | Theorems.Thm_KServer_potential_push_first
-- name    : KServer.potential_push_first
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-01T06:45:48.649414+00:00
-- url     : https://prove2.me/theorems/b95be347-c330-495a-af44-a6fa943e3d8f
-- title:
--   Pushing the request from the first anchor slot to the last
-- statement:
--   Let $w$ be the work function of a $3$-server instance ending with the request $r$, in the antipodal extension of a bounded metric space. The anchored potential $\Phi_{x_1x_2x_3}(w) = w(x_1x_2x_3) + w(\bar x_1 x_2 x_3) + w(\bar x_2\bar x_2 x_3) + w(\bar x_3^{\,3})$ has a common first summand for all orderings of a fixed triple, so comparing anchored potentials over reorderings compares the last three summands. The theorem states, in that reduced form: for any $y, z$,
--
--   $$\Phi_{yzr}(w) \le \Phi_{ryz}(w) \qquad \text{or} \qquad \Phi_{zyr}(w) \le \Phi_{ryz}(w):$$
--
--   **the request can be pushed from the first anchor slot to the last**, at the price of possibly transposing the other two anchors. Together with the middle-slot push this completes Lemma 21 of Coester and Koutsoupias for $k=3$: the minimum of the potential over orderings of a fixed anchor triple containing $r$ is attained with $r$ last. (Remarkably, this pushing lemma is false for $k = 4$; it is the step that confines the potential method, in this form, to three servers.)
--
--   ## Structure of the proof
--
--   The configuration $\bar y\,\bar y\,z$ resolves. If a $\bar y$-server resolves (cost $2\Delta - ry$), a single Lipschitz move $w(\bar r\bar r z) \le w(\bar r y z) + (2\Delta - yr)$ lands the first three summands on those of $\Phi_{yrz}$, and the middle-slot push finishes.
--
--   If instead $z$ resolves, the all-antipodes value of $z$ expands exactly ($w(\bar z^3) = w(\bar z\bar z r) + 2\Delta - rz$, the resolution being forced), and the resolution dichotomy for $(\bar r, y, z)$ --- such a configuration always resolves through one of its *original* servers --- splits the argument. If it resolves from $y$, quasiconvexity of the work function applied to the pair $(r,\bar y,\bar y), (r,\bar r, z)$ with the request as common point, followed by the Lipschitz bound $w(\bar r^3) \le w(r, \bar y, \bar r) + 2\Delta + yr$, closes the first disjunct; if from $z$, the mirror argument with $(r, \bar z, \bar z), (r, \bar r, y)$ closes the second. Each branch is a linear assembly of the substituted identities.
--
--   ## Role
--
--   In the case analysis of Theorem 23 (WFA is $3$-competitive on trees), whenever the minimising anchor triple resolves from its first or second anchor, the analysis produces an anchored potential with $r$ in the first slot; this lemma relocates $r$ to the last slot, which is the form the update property of the potential consumes. No tree structure is used --- resolution, quasiconvexity, Lipschitzness, and the antipodal distance algebra suffice.
-- source:
--   C. Coester, E. Koutsoupias, 'Towards the k-server conjecture: a unifying potential, pushing the frontier to the circle', ICALP 2021, arXiv:2102.10474, Lemma 21 (lem:push3), the main case π(k−2) = r, for k = 3; the paper remarks the lemma fails for k = 4.

import Mathlib
import Definitions.Def_KServer_workfunctionU
import Definitions.Def_KServer_antipodal_extension

namespace KServer

theorem potential_push_first (M : Type) [MetricSpace M] (Δ : ℝ) (hΔ0 : 0 < Δ)
    (hΔ : ∀ u v : M, dist u v ≤ Δ) (C₀ : Config 3 M) (σ : List M) (r y z : M) :
    (@workFnU 3 (M ⊕ M) (antipodalExtension M Δ hΔ0 hΔ)
          (fun i => Sum.inl (C₀ i)) ((σ ++ [r]).map Sum.inl) ![Sum.inr y, Sum.inl z, Sum.inl r]
        + @workFnU 3 (M ⊕ M) (antipodalExtension M Δ hΔ0 hΔ)
          (fun i => Sum.inl (C₀ i)) ((σ ++ [r]).map Sum.inl) ![Sum.inr z, Sum.inr z, Sum.inl r]
        + @workFnU 3 (M ⊕ M) (antipodalExtension M Δ hΔ0 hΔ)
          (fun i => Sum.inl (C₀ i)) ((σ ++ [r]).map Sum.inl) ![Sum.inr r, Sum.inr r, Sum.inr r]
      ≤ @workFnU 3 (M ⊕ M) (antipodalExtension M Δ hΔ0 hΔ)
          (fun i => Sum.inl (C₀ i)) ((σ ++ [r]).map Sum.inl) ![Sum.inr r, Sum.inl y, Sum.inl z]
        + @workFnU 3 (M ⊕ M) (antipodalExtension M Δ hΔ0 hΔ)
          (fun i => Sum.inl (C₀ i)) ((σ ++ [r]).map Sum.inl) ![Sum.inr y, Sum.inr y, Sum.inl z]
        + @workFnU 3 (M ⊕ M) (antipodalExtension M Δ hΔ0 hΔ)
          (fun i => Sum.inl (C₀ i)) ((σ ++ [r]).map Sum.inl) ![Sum.inr z, Sum.inr z, Sum.inr z])
    ∨ (@workFnU 3 (M ⊕ M) (antipodalExtension M Δ hΔ0 hΔ)
          (fun i => Sum.inl (C₀ i)) ((σ ++ [r]).map Sum.inl) ![Sum.inr z, Sum.inl y, Sum.inl r]
        + @workFnU 3 (M ⊕ M) (antipodalExtension M Δ hΔ0 hΔ)
          (fun i => Sum.inl (C₀ i)) ((σ ++ [r]).map Sum.inl) ![Sum.inr y, Sum.inr y, Sum.inl r]
        + @workFnU 3 (M ⊕ M) (antipodalExtension M Δ hΔ0 hΔ)
          (fun i => Sum.inl (C₀ i)) ((σ ++ [r]).map Sum.inl) ![Sum.inr r, Sum.inr r, Sum.inr r]
      ≤ @workFnU 3 (M ⊕ M) (antipodalExtension M Δ hΔ0 hΔ)
          (fun i => Sum.inl (C₀ i)) ((σ ++ [r]).map Sum.inl) ![Sum.inr r, Sum.inl y, Sum.inl z]
        + @workFnU 3 (M ⊕ M) (antipodalExtension M Δ hΔ0 hΔ)
          (fun i => Sum.inl (C₀ i)) ((σ ++ [r]).map Sum.inl) ![Sum.inr y, Sum.inr y, Sum.inl z]
        + @workFnU 3 (M ⊕ M) (antipodalExtension M Δ hΔ0 hΔ)
          (fun i => Sum.inl (C₀ i)) ((σ ++ [r]).map Sum.inl) ![Sum.inr z, Sum.inr z, Sum.inr z]) := by sorry

end KServer
