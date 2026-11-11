-- Prove2me | Theorems.Thm_KMedianPP_Tight_lemma_4_6
-- name    : KMedianPP.Tight.lemma_4_6
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T16:03:42.330206+00:00
-- url     : https://prove2.me/theorems/e9430573-2f9a-4f76-b3c7-2812bc056cc3
-- title:
--   Lemma 4.6 — for $\Delta>0$, $\Gamma=\Delta$: $\mathbb E[U_{\mathrm{final}}\mid S]\le\Phi_{r,s}(A,U)$ at every state
-- statement:
--   Let $\Delta>0$ and $\Gamma=\Delta$ (§4.2.1), and fix a balancing construction with constant $\alpha$ and (P1)–(P3). Consider any state with $r$ unsettled clusters, $s$ samples remaining with $m=r+\Delta-s\ge0$, miss proxy $A$ and total balanced mass $U$. Then
--   $$\mathbb E[U_{\mathrm{final}}\mid S]\le\Phi_{r,s}(A,U)=m\,p_{r,s}\frac Ur+\big(R_{r,s}-m\,p_{r,s}\big)\frac A\Gamma\quad(r\ge1),\qquad \Phi_{0,s}=0,$$
--   where $U_{\mathrm{final}}$ is the total balanced mass of the unsettled clusters after the remaining $s$ samples of the hit/miss process.
--
--   Differences from the source:
--   - encoding: a finite (multi)set X ⊆ M of input points → `X : Fin n → M` (input point i is `X i`; repeated points allowed); reason: a finite multiset is an indexed family; same instances
--   - encoding: current center set C ⊆ M, D(x) = d(x, C) → the indices `S : Finset (Fin n)` of the sampled input points, `D(x) = distTo X S x` (minimum over S); reason: D^ℓ-sampling only ever samples input points; same distances
--   - generalization: a fixed optimal solution with clusters P_1, …, P_k and optimal centers c*_1, …, c*_k (§2, p. 9) → any reference clustering: `σ : Fin n → Fin k` (P_j = {i : σ i = j}) and centers `c : Fin k → M`, with ϕ(P_j) = `phi X σ c ℓ j`; reason: the analysis never uses optimality or nearest-center assignment (only d*_x = d(x, c*_j) and the triangle inequality); an optimal solution is one such clustering, so the statement specializes to the source's
--   - encoding: §2 standing assumption: a fixed distance exponent ℓ > 0 → hypothesis `0 < ℓ`; reason: the section's standing assumption made explicit
--   - encoding: D(x)^ℓ, (d*_x)^ℓ for real ℓ > 0 → `Real.rpow` (`^` with a real exponent) of nonnegative reals; reason: same values
--   - encoding: §4 standing assumption: a balancing construction with constant α_ℓ satisfying (P1)–(P3) (pp. 10, 14) → balanced masses `b : Finset (Fin n) → Fin n → ℝ` with `IsBalancingConstruction X σ c ℓ α b`: 0 ≤ b(x) ≤ D(x)^ℓ, (P1), (P2), (P3) for every cluster P_j that can be unsettled at the center set S (`CanBeUnsettled σ S j`: some current center outside P_j); reason: the properties as stated on p. 10, for unsettled clusters; the first center settles its own cluster, so P_j can be unsettled at S exactly when some center of S lies outside P_j; a construction is given by its balanced masses
--   - generalization: "any fixed state S of the actual process with r unsettled clusters, s samples remaining" (so m = r + Δ − s ≥ 0) → any pair (S, H) in which the cluster of some current center is settled (`∃ i ∈ S, σ i ∈ H`: the first center settles its cluster, §3 p. 9) and `s ≤ unsettledCount H + Δ`; reason: every reachable state is such a pair with m ≥ 0; the statement also covers unreachable pairs
--   - encoding: a sample x ∈ P of an unsettled cluster is a hit with probability b(x)/D(x)^ℓ, otherwise a miss; samples from settled clusters are misses → `hitProb`/`missProb` S H i = (hit / miss mass at x_i) / cost(C); a hit of P_{σ i} moves to (S ∪ {i}, H ∪ {σ i}), a miss to (S ∪ {i}, H); reason: the joint law of (sampled point, hit/miss) of p. 11 and p. 14
--   - encoding: r = number of unsettled clusters → `unsettledCount H = |univ \ H|`; reason: same number
--   - encoding: §4.2.1 standing assumptions Δ > 0 and Γ = Δ → hypothesis `0 < Δ` and `Phi (Δ : ℝ) Δ …`; reason: the section's standing assumptions made explicit
--   - encoding: E[U_final | S] → `finalExp … (balTotal σ b) s S H`: exact expectation over the hit/miss process (sampled points and the hit/miss randomization), stopping when cost(C) = 0; reason: the same process; after the algorithm stops U stays fixed
-- source:
--   Kaplan, Naori, Tight Bounds for k-Median++ and Improved Bounds for k-Means++, STOC 2027 submission (manuscript sha256 f017529e…), p. 18 (PDF 20), Lemma 4.6 and (12)

import Mathlib
import Definitions.Def_KMedianPP_Tight_Sampling
import Definitions.Def_KMedianPP_Tight_EqualMass
import Definitions.Def_KMedianPP_Tight_Balancing

set_option autoImplicit false

namespace KMedianPP.Tight

/-- Lemma 4.6 (p. 18), under §4.2.1's standing `Δ > 0` and `Γ = Δ`: for any state of the process
with `r` unsettled clusters, `s` samples remaining (`m = r + Δ - s ≥ 0` past misses), miss proxy
`A` and total balanced mass `U`, `E[U_final | S] ≤ Φ_{r,s}(A, U)`.
A state `(S, H)` has the cluster of some current center (the first center) settled, `σ i ∈ H`
for some `i ∈ S` (§3, p. 9). -/
theorem lemma_4_6 {M : Type*} [MetricSpace M] {n k : ℕ} (X : Fin n → M) (σ : Fin n → Fin k)
    (c : Fin k → M) (ℓ α : ℝ) (hℓ : 0 < ℓ) (b : Finset (Fin n) → Fin n → ℝ)
    (hb : IsBalancingConstruction X σ c ℓ α b) (Δ : ℕ) (hΔ : 0 < Δ)
    (S : Finset (Fin n)) (H : Finset (Fin k)) (hSH : ∃ i ∈ S, σ i ∈ H) (s : ℕ)
    (hs : s ≤ unsettledCount H + Δ) :
    finalExp X σ ℓ b (balTotal σ b) s S H ≤
      Phi (Δ : ℝ) Δ (unsettledCount H) s (missProxy X σ c ℓ α S H) (balTotal σ b S H) := by sorry

end KMedianPP.Tight
