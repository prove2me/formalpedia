-- Prove2me | Theorems.Thm_HardCoreBochner_theorem_1_1
-- name    : HardCoreBochner.theorem_1_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T17:32:04.764866+00:00
-- url     : https://prove2.me/theorems/2957a982-c0b4-4b69-a52d-60a06d6c89b7
-- title:
--   Theorem 1.1 — hard-core Glauber dynamics mixes in $O((n^2/\delta)\log(1+1/\lambda))$ steps when $\lambda\le(1-\delta)/(-\lambda_{\min}(A_G)-1)$
-- statement:
--   There is an absolute constant $C>0$ such that the following holds. Let $\delta\in(0,1)$, and consider Glauber dynamics $P_{GD}$ for the hard-core model on a finite graph $G$ with $n$ vertices and activity $\lambda>0$. Let $\lambda_{\min}(A_G)$ be the minimum eigenvalue of the adjacency matrix $A_G$ of $G$, assume $-\lambda_{\min}(A_G)-1>0$, and suppose
--   $$\lambda\le\frac{1-\delta}{-\lambda_{\min}(A_G)-1}.$$
--   Then
--   $$T_{\mathrm{mix}}(P_{GD})\le C\,\frac{n^2}{\delta}\log\Big(1+\frac1\lambda\Big),$$
--   where $T_{\mathrm{mix}}(P_{GD})=\max_\sigma\min\{t\ge0:d_{TV}(P^t_{GD}(\sigma,\cdot),\mu)<1/4\}$: from every independent set $\sigma$ some $t\le C(n^2/\delta)\log(1+1/\lambda)$ has $d_{TV}(P^t_{GD}(\sigma,\cdot),\mu_{G,\lambda})<1/4$.
--
--   This is the theorem of Chen, Chen, Chen, Yin and Zhang [8, Theorem 1.2]. On a random $\Delta$-regular graph, where $\lambda_{\min}(A_G)\approx-2\sqrt{\Delta-1}$, it gives rapid mixing for $\lambda$ up to about $(1-\delta)/(2\sqrt{\Delta-1}-1)$, beyond the tree-uniqueness threshold.
--
--   Differences from the source:
--   - reading: λ ≤ (1 − δ)/(−λ_min(A_G) − 1), whose denominator is 0 when λ_min(A_G) = −1 → 0 < −lamMin G − 1 and lam ≤ (1 − δ)/(−lamMin G − 1); reason: the fraction is undefined at denominator 0; the reading (1 − δ)/0 = +∞ is false (G = K₂: T_mix ≥ cλ while (n²/δ)log(1 + 1/λ) → 0 as λ → ∞); Lean's literal (1 − δ)/0 = 0 already forces λ ≤ 0, so the explicit hypothesis changes nothing and makes the case visible; for λ_min(A_G) > −1 the printed bound is negative and no λ > 0 qualifies
--   - encoding: T_mix(P_GD) ≤ O((n²/δ) log(1 + 1/λ)) → ∃ C > 0, chosen before V, G, δ and λ, bounding the mixing time by C (n²/δ) log(1 + 1/λ); reason: the O(·) is a single absolute constant; same statement
--   - encoding: T_mix(P) = max_σ min{t ≥ 0 : d_TV(P^t(σ,·), µ) < 1/4} ≤ B → ∀ σ, ∃ t : ℕ, t ≤ B ∧ tvDist (rowDist P t σ) µ < 1/4; reason: max_σ min{…} ≤ B holds exactly when every start has such a t; the ∃ form has no sInf of an empty set
--   - encoding: Glauber dynamics for the hard-core model on the independent sets of G → hcChain G λ = MarkovMixing.subChain (MarkovMixing.glauber (MarkovMixing.hardcoreDist G λ)) (MarkovMixing.IsHardcore G); reason: the published heat-bath chain for the published hard-core law, restricted to the independent sets; off the diagonal it is (1)
--   - encoding: a finite graph on any vertex set → V : Type (universe 0); reason: every finite set is in bijection with some Fin n, which lives in Type; the constant is chosen before V, so no instance is lost
-- source:
--   Göbel, Jenssen, Michelen, Pappik, Perkins, Schiller, A simple proof of rapid mixing on random regular graphs beyond uniqueness, arXiv:2606.27545 (version of 2026-11-03, sha256 dfc58c3b6107de9702dda27883f2839093b816f7a6f9c543fcb2be0ad91ad6ad), Theorem 1.1, p.3 (PDF p.3)

import Definitions.Def_mm_coupling
import Definitions.Def_mm_mcmc
import Definitions.Def_mm_mixing
import Definitions.Def_HardCoreBochner_lamMin
import Definitions.Def_HardCoreBochner_hcChain

namespace HardCoreBochner

/-- **Theorem 1.1** (Chen, Chen, Chen, Yin, Zhang [8, Theorem 1.2]). Göbel, Jenssen, Michelen, Pappik, Perkins, Schiller, *A simple proof of rapid mixing on random
regular graphs beyond uniqueness*, arXiv:2606.27545 (version of 2026-11-03, sha256 dfc58c3b…), Theorem 1.1, p.3.

Let `δ ∈ (0,1)` and consider Glauber dynamics for the hard-core model on a graph `G` with `n`
vertices and activity `λ > 0`. If `λ ≤ (1 − δ)/(−λ_min(A_G) − 1)`, where `λ_min(A_G)` is the minimum
eigenvalue of the adjacency matrix of `G`, then `T_mix(P_GD) ≤ O((n²/δ) log(1 + 1/λ))`.

**Formalization Note**
1. The `O(·)` is one absolute constant `C > 0`, chosen before the vertex type, the graph, `δ` and `λ`.
2. `T_mix(P_GD) = max_σ min{t ≥ 0 : d_TV(P^t_GD(σ,·), µ) < 1/4}` (p.2, strict `< 1/4`, worst start) is
   at most `B` exactly when every independent set `σ` has some `t ≤ B` with `d_TV < 1/4`; that is the
   conclusion, so no `sInf` junk enters.
3. The denominator `−λ_min(A_G) − 1` is required to be positive. When `λ_min(A_G) = −1` (a disjoint
   union of cliques with an edge) the printed fraction has denominator `0`; reading `(1 − δ)/0` as `+∞`
   makes the statement false: for `G = K₂` from `{1}` the chain leaves only through `∅`, with
   probability `1/(2(1 + λ))` per step, so `T_mix ≥ cλ`, while `(n²/δ) log(1 + 1/λ) → 0` as `λ → ∞`.
   Lean's own reading `(1 − δ)/0 = 0` already excludes this case (it forces `λ ≤ 0`); the explicit
   hypothesis makes it visible. When `λ_min(A_G) > −1` (edgeless `G`) the printed bound is negative
   and no `λ > 0` satisfies it.
4. Configurations are `V → Bool`; `P_GD` is `hcChain G λ`, the published heat-bath
   `MarkovMixing.glauber` for the published `MarkovMixing.hardcoreDist G λ`, restricted to the
   independent sets by `MarkovMixing.subChain`; `d_TV` and `P^t(σ,·)` are the published `tvDist`
   and `rowDist`. `n` is `Fintype.card V`. -/
theorem theorem_1_1 :
    ∃ C : ℝ, 0 < C ∧ ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
      [DecidableRel G.Adj] (δ lam : ℝ), 0 < δ → δ < 1 → 0 < lam → 0 < -lamMin G - 1 →
        lam ≤ (1 - δ) / (-lamMin G - 1) →
        ∀ σ : {σ : V → Bool // MarkovMixing.IsHardcore G σ}, ∃ t : ℕ,
          (t : ℝ) ≤ C * ((Fintype.card V : ℝ) ^ 2 / δ) * Real.log (1 + 1 / lam) ∧
            MarkovMixing.tvDist (MarkovMixing.rowDist (hcChain G lam) t σ) (hcLaw G lam) < 1 / 4 := by sorry

end HardCoreBochner
