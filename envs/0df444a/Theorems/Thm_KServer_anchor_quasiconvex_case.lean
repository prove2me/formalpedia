-- Prove2me | Theorems.Thm_KServer_anchor_quasiconvex_case
-- name    : KServer.anchor_quasiconvex_case
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-01T07:25:59.751277+00:00
-- url     : https://prove2.me/theorems/0dfdc73a-c8de-47d0-be61-cd3cf635e86e
-- title:
--   The quasiconvexity case of the anchoring theorem
-- statement:
--   Let $\Phi_{x_1x_2x_3}$ be the anchored Coester--Koutsoupias potential of a $3$-server instance ending with the request $r$, in the antipodal extension of a bounded space. Suppose the three resolutions of the final case of Coester--Koutsoupias' Theorem 23 hold: the triple resolves in its third slot ($w(x_1x_2x_3) = w(x_1x_2r) + d(r,x_3)$), its first-anchor antipodal companion resolves in the middle slot ($w(\bar x_1x_2x_3) = w(\bar x_1 r x_3) + d(r,x_2)$), and the doubled antipode of the second anchor resolves through an antipodal server ($w(\bar x_2\bar x_2 x_3) = w(\bar x_2 r x_3) + 2\Delta - d(r,x_2)$). Then
--
--   $$\Phi_{x_2x_3r}(w) \le \Phi_{x_1x_2x_3}(w) \qquad \text{or} \qquad \Phi_{x_1x_3r}(w) \le \Phi_{x_1x_2x_3}(w).$$
--
--   ## Role
--
--   This is the last case of the case analysis behind Theorem 23 --- the one Coester and Koutsoupias close "using only quasiconvexity of $w$". The three resolutions rewrite all four summands of $\Phi_{x_1x_2x_3}$ into work-function values at configurations containing the request (the fourth summand's resolution, $w(\bar x_3^3) = w(\bar x_3\bar x_3 r) + 2\Delta - d(r,x_3)$, is forced, all three coordinates being equal), at a total additive cost of exactly $4\Delta$. Quasiconvexity in its three-point form, with the request as the common coordinate, then exchanges the pairs $(x_1, x_2)$ and $(\bar x_1, x_3)$: the pairing $(x_1\bar x_1),(x_2x_3)$ leads to $\Phi_{x_2x_3r}$, the crossing $2\Delta = d(\bar r, x_1) + d(\bar r, \bar x_1)$ absorbing the hybrid $w(r x_1 \bar x_1)$ into $w(\bar r^3)$; the pairing $(x_1x_3),(x_2\bar x_1)$ leads to $\Phi_{x_1x_3r}$, re-using the middle-slot resolution and the Lipschitz bound $w(\bar r^3) \le w(\bar x_2 r x_3) + 4\Delta + d(x_2,r) - d(x_3,r)$. Each branch is exact up to a discarded non-negative multiple of $\Delta$.
--
--   Applied to the swap-symmetric minimising triple of Lemma 25, this exhibits the potential's minimum at a triple ending with the request whenever the deep case of the analysis is reached.
--
--   ## Formalization note
--
--   Stated in the antipodal extension on $M \oplus M$ with originals embedded by `Sum.inl`; all distances are literal ($d(\mathrm{inl}\,a, \mathrm{inr}\,b) = 2\Delta - d(a,b)$). No tree structure is used in this case, and the conclusion is a disjunction because quasiconvexity chooses the pairing.
-- source:
--   C. Coester, E. Koutsoupias, 'Towards the k-server conjecture', ICALP 2021, arXiv:2102.10474, proof of Theorem 23, final case: 'For these resolutions, we can conclude 3-competitiveness using only quasiconvexity of w', both pairings.

import Mathlib
import Definitions.Def_KServer_workfunctionU
import Definitions.Def_KServer_antipodal_extension
import Definitions.Def_KServer_ck_potential

namespace KServer

theorem anchor_quasiconvex_case (M : Type) [MetricSpace M] (Δ : ℝ) (hΔ0 : 0 < Δ)
    (hΔ : ∀ u v : M, dist u v ≤ Δ) (C₀ : Config 3 M) (σ : List M) (r x₁ x₂ x₃ : M)
    (h0 : @workFnU 3 (M ⊕ M) (antipodalExtension M Δ hΔ0 hΔ)
          (fun i => Sum.inl (C₀ i)) ((σ ++ [r]).map Sum.inl) ![Sum.inl x₁, Sum.inl x₂, Sum.inl x₃]
        = @workFnU 3 (M ⊕ M) (antipodalExtension M Δ hΔ0 hΔ)
          (fun i => Sum.inl (C₀ i)) ((σ ++ [r]).map Sum.inl) ![Sum.inl x₁, Sum.inl x₂, Sum.inl r]
          + dist r x₃)
    (h1 : @workFnU 3 (M ⊕ M) (antipodalExtension M Δ hΔ0 hΔ)
          (fun i => Sum.inl (C₀ i)) ((σ ++ [r]).map Sum.inl) ![Sum.inr x₁, Sum.inl x₂, Sum.inl x₃]
        = @workFnU 3 (M ⊕ M) (antipodalExtension M Δ hΔ0 hΔ)
          (fun i => Sum.inl (C₀ i)) ((σ ++ [r]).map Sum.inl) ![Sum.inr x₁, Sum.inl r, Sum.inl x₃]
          + dist r x₂)
    (h2 : @workFnU 3 (M ⊕ M) (antipodalExtension M Δ hΔ0 hΔ)
          (fun i => Sum.inl (C₀ i)) ((σ ++ [r]).map Sum.inl) ![Sum.inr x₂, Sum.inr x₂, Sum.inl x₃]
        = @workFnU 3 (M ⊕ M) (antipodalExtension M Δ hΔ0 hΔ)
          (fun i => Sum.inl (C₀ i)) ((σ ++ [r]).map Sum.inl) ![Sum.inr x₂, Sum.inl r, Sum.inl x₃]
          + (2 * Δ - dist r x₂)) :
    ckPotAt M Δ hΔ0 hΔ C₀ (σ ++ [r]) x₂ x₃ r ≤ ckPotAt M Δ hΔ0 hΔ C₀ (σ ++ [r]) x₁ x₂ x₃
    ∨ ckPotAt M Δ hΔ0 hΔ C₀ (σ ++ [r]) x₁ x₃ r ≤ ckPotAt M Δ hΔ0 hΔ C₀ (σ ++ [r]) x₁ x₂ x₃ := by sorry

end KServer
