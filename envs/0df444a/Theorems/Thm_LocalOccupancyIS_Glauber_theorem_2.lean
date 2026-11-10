-- Prove2me | Theorems.Thm_LocalOccupancyIS_Glauber_theorem_2
-- name    : LocalOccupancyIS.Glauber.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T10:59:07.817278+00:00
-- url     : https://prove2.me/theorems/8973d0ee-c7da-4db2-bb16-e9a634c08cf5
-- title:
--   Theorem 2 — fixed-word and averaged-prefix Glauber transfer
-- statement:
--   Let $G$ be a nonempty finite simple graph with degree bound $\Delta$, and let $\lambda,\beta,\gamma>0$ and $0\le\eta<1$. Fix, independently of the evolving state and every random choice, one finite word of neighbors for each center $u$. Let $S_u$ be the corresponding product of single-site updates and let $\kappa$ be the maximum total number of occurrences of any vertex across all full words. Assume that for every input probability law $\nu$ and every $u$,
--
--   $$\beta\mathbb P_{\nu S_uP_u}(u\in I)+\gamma\mathbb E_{\nu S_u}|I\cap N(u)|\ge1-\eta,$$
--
--   or assume the arithmetic average of these same quantities over a nonempty collection of fixed prefixes of $S_u$ is at least $1-\eta$. In the latter case $\kappa$ still counts the full words. Put $p=\lambda/(1+\lambda)$, $\Gamma=\beta+\gamma\Delta$, $C=\beta+\kappa\max\{\beta p,\gamma\Delta\}$, $H_0=D_{KL}(\nu_0\|\pi)$ and $H_\lambda=n\log((1+\lambda)/\min\{1,\lambda\})$. For any initial probability law and any integer $T\ge1$, ordinary random-scan Glauber dynamics and independent uniform $J\in\{0,\ldots,T-1\}$ obey
--
--   $$\mathbb E|I_J|\ge\frac n\Gamma\left(1-\eta-C\sqrt{\frac{H_0}{2T}}\right).$$
--
--   The theorem also asserts $H_0\le H_\lambda$ and the resulting bound $(1-\eta-\varepsilon)n/\Gamma$ whenever $0<\varepsilon<1$ and $T\ge C^2H_\lambda/(2\varepsilon^2)$. No equilibrium local-occupancy assumption is added. This transfers either certificate to actual ordinary dynamics.
--
--   Differences from the source:
--   - encoding: finite independent sets and induced subgraphs → Boolean configurations on finite types and induced subtypes; reason: these presentations preserve all feasible configurations, including the empty one
--   - encoding: a uniform random site in ordinary Glauber dynamics → an explicit nonempty vertex type; the published random-scan matrix equals the average of the single-site kernels; reason: a uniform site is defined on precisely this implicit source domain; no empty-graph extension or extra nonempty hypothesis on a previously defined process is asserted
--   - encoding: the two occupancy expressions in equations (4) and (6) → the identical expectation of the score beta p times the empty-neighborhood indicator plus gamma times neighborhood cardinality; reason: the single-site heat-bath proposal gives the indicated center occupation probability exactly
-- source:
--   Ewan Davies, Brian Tan, STOC 2027 submission #982 (October 2026), Theorem 2, p. 4; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/982.pdf#page=4

import Definitions.Def_LocalOccupancyIS_Glauber_Parameters

namespace LocalOccupancyIS.Glauber
/-- Theorem 2, p.4: both certificates, the entropy error, and its finite-time consequence. -/
theorem theorem_2 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (Δ : ℕ) (hΔ : DegreeBound G Δ)
    (lam β γ η : ℝ) (hlam : 0 < lam) (hβ : 0 < β) (hγ : 0 < γ)
    (hη : 0 ≤ η ∧ η < 1) (w : V → List V) (hw : NeighborhoodWords G w)
    (hc : WordCertificate G lam β γ η w ∨
      ∃ a : V → List ℕ, Prefixes w a ∧ PrefixCertificate G lam β γ η w a)
    (ν : State G → ℝ) (hν : MarkovMixing.IsDist ν) :
    let H₀ := kl ν (HardCoreBochner.hcLaw G lam)
    let Hlam := entropyBound (Fintype.card V) lam
    let Γ := β + γ * Δ
    let C := transferConstant Δ (occurrences w) lam β γ
    MarkovMixing.IsStochastic (K G lam) ∧
    K G lam = (Fintype.card V : ℝ)⁻¹ • ∑ u, P G lam u ∧
    H₀ ≤ Hlam ∧
    ∀ T : ℕ, 1 ≤ T →
      timeMean G lam ν T ≥ Fintype.card V / Γ * (1 - η - C * Real.sqrt (H₀ / (2*T))) ∧
      ∀ ε : ℝ, 0 < ε → ε < 1 → C^2 * Hlam / (2*ε^2) ≤ T →
        timeMean G lam ν T ≥ (1-η-ε)*Fintype.card V/Γ := by sorry
end LocalOccupancyIS.Glauber
