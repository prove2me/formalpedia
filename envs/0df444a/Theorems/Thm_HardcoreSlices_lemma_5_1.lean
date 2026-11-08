-- Prove2me | Theorems.Thm_HardcoreSlices_lemma_5_1
-- name    : HardcoreSlices.lemma_5_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T06:39:52.666673+00:00
-- url     : https://prove2.me/theorems/9b09d592-f045-45c9-8a67-e2d512ac740a
-- title:
--   Lemma 5.1 — top-link expansion of the one-sided slice (corrected: positive denominator)
-- statement:
--   Let $G=(X,Y,E)$ be a $\Delta$-regular bipartite graph, $\lambda>0$, $k\le|X|$, and $\tau\subseteq X$ with $|\tau|=k-2$. Assume that $|N_\tau(u)\cap N_\tau(v)|\le2$ for all distinct $u,v\in\mathcal X_\tau(1)$, and that no $u\in\mathcal X_\tau(1)$ shares $2$ common neighbours with more than one other vertex in $G$. Let $\Delta_\tau=\mathbf E_{v\sim\mathcal X_\tau(1)}|N_\tau(v)|$ under the uniform measure, and assume $(1+\lambda)^{\Delta_\tau}<|X|-|\tau|$. Then
--   $$\lambda_2(P_\tau)\le\frac{\max\{\lambda\cdot\lambda_2(A_G)^2+\lambda^2-1,\,0\}\cdot(1+\lambda)^{\Delta_\tau}}{|X|-|\tau|-(1+\lambda)^{\Delta_\tau}}.$$
--   The same holds with $X$ and $Y$ exchanged. This deterministic bound gives Theorem 1.9.
--
--   Differences from the source:
--   - correction: and |X| is large enough → (1 + λ)^∆τ < |X| − |τ|; reason: k is free, so large |X| does not make the denominator positive: m = 8, ∆ = 2, λ = 1, G disjoint copies of K_{2,2}, k = |X|, τ all of X outside one copy has ∆τ = 2, bound −8 and λ2(Pτ) = −1
--   - encoding: λ2(Pτ) ≤ b → HDXConc.SecondEigLE in Rayleigh form; reason: equivalent by Courant–Fischer for a reversible walk on at least two vertices, with no eigenvalue sort
--   - generalization: τ ⊆ X → τ in either side; reason: the graph is symmetric in the sides; the source is b = false
-- source:
--   Kocurek, Oveis Gharan, Tjowasi, Sampling from the Hardcore Model on Random Regular Bipartite Graphs above the Uniqueness Threshold, arXiv:2604.21847 (version held, sha256 363c225d…), Lemma 5.1, p.22

import Mathlib
import Definitions.Def_HardcoreSlices_oneSidedSlice
import Definitions.Def_HardcoreSlices_lam2
import Definitions.Def_HDXConc_linkWeight
import Definitions.Def_HDXConc_SecondEigLE

open Classical

namespace HardcoreSlices

open ExpanderBIS.RandomHardCore

/-- **Lemma 5.1 (corrected: positive denominator).** Kocurek, Oveis Gharan, Tjowasi, *Sampling from the Hardcore Model on Random Regular Bipartite Graphs above the Uniqueness Threshold*, arXiv:2604.21847 (version held, sha256 363c225d…), p.22: "Fix `k ≤ |X|` and let `(X, µλ^(k))` be the one-sided slice of the hardcore model of a `∆`-regular bipartite graph
`G = (X, Y, E)` at fugacity `λ > 0`. Let `τ ⊆ X` satisfy `codim(τ) = 2`. Finally, assume `max_{u≠v∈Xτ(1)} |Nτ(u) ∩ Nτ(v)| ≤ 2` and no vertex `u ∈ Xτ(1)` shares 2
common neighbors with more than one other vertex in `G`. Then, `λ2(Pτ) ≤ max{λ · λ2(AG)² + λ² − 1, 0} · (1 + λ)^∆τ / ( |X| − |τ| − (1 + λ)^∆τ )`, where
`∆τ := E_{v∼Xτ(1)}[|Nτ(v)|]` and |X| is large enough."

**Formalization Note.** Deterministic in `G`; `b` picks the side. "Large enough" is replaced by the hypothesis `(1 + λ)^∆τ < |X| − |τ|` that it stands for: otherwise the denominator is `≤ 0`
and the bound false. Counterexample: `m = 8`, `∆ = 2`, `λ = 1`, `G` a disjoint union of copies of `K_{2,2}`, `k = |X|`, `τ` all of `X` outside one copy: all
assumptions hold, `∆τ = 2`, the bound is `−8`, and `λ2(Pτ) = −1`. The power is the real power, as `∆τ` need not be an integer. -/
theorem lemma_5_1 {m Δ : ℕ} (G : SimpleGraph (Vertex m)) (hG : IsBipReg G Δ) (lam : ℝ) (hlam : 0 < lam)
    (b : Bool) (k : ℕ) (hk : k ≤ m) (τ : Finset (Vertex m)) (hτ : τ ⊆ sideOf m b) (hcod : τ.card + 2 = k)
    (h₁ : ∀ u ∈ oneSidedLink (sideOf m b) k τ, ∀ v ∈ oneSidedLink (sideOf m b) k τ, u ≠ v →
      (nbrTau G τ u ∩ nbrTau G τ v).card ≤ 2)
    (h₂ : ∀ u ∈ oneSidedLink (sideOf m b) k τ, ∀ v₁ v₂ : Vertex m, v₁ ≠ u → v₂ ≠ u → v₁ ≠ v₂ →
      2 ≤ (vertexBoundary G {u} ∩ vertexBoundary G {v₁}).card →
      2 ≤ (vertexBoundary G {u} ∩ vertexBoundary G {v₂}).card → False)
    (hden : (1 + lam) ^ deltaTau G (sideOf m b) k τ < (m : ℝ) - τ.card) :
    HDXConc.SecondEigLE (oneSidedLink (sideOf m b) k τ)
      (HDXConc.linkWeight (oneSidedComplex (sideOf m b) k) k (oneSidedLaw G lam (sideOf m b) k) τ)
      (max (lam * lam2 G ^ 2 + lam ^ 2 - 1) 0 * (1 + lam) ^ deltaTau G (sideOf m b) k τ /
        ((m : ℝ) - τ.card - (1 + lam) ^ deltaTau G (sideOf m b) k τ)) := by sorry

end HardcoreSlices
