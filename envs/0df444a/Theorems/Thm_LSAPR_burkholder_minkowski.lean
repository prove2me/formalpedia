-- Prove2me | Theorems.Thm_LSAPR_burkholder_minkowski
-- name    : LSAPR.burkholder_minkowski
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:33:16.965421+00:00
-- url     : https://prove2.me/theorems/c4c8df4b-db0b-4aa7-9eca-5dfaed08053a
-- title:
--   (50) — Burkholder's inequality plus Minkowski: $\mathbb E^{1/p}\|\sum D_i\|^p\le p(\sum\mathbb E^{2/p}\|D_i\|^p)^{1/2}$ for $\mathbb R^d$-valued martingale differences
-- statement:
--   Let $(\mathcal F_i)$ be a filtration on a probability space, and let $D_0,\dots,D_{m-1}$ be integrable $\mathbb R^d$-valued random vectors with $D_i$ being $\mathcal F_{i+1}$-measurable and $\mathbb E[D_i\mid\mathcal F_i]=0$ almost surely. Then for every real $p\ge2$,
--   $$\mathbb E^{1/p}\Big[\Big\|\sum_{i<m}D_i\Big\|^p\Big]\le p\Big(\sum_{i<m}\mathbb E^{2/p}\big[\|D_i\|^p\big]\Big)^{1/2}.$$
--
--   The paper uses this step twice in the proof of Theorem 2 and once in the proof of Proposition 6, citing Osekowski (2012, Theorem 8.6).
--
--   Differences from the source:
--   - generalization: two instances: the sequences Ã_{t+1}H⁽¹⁾_t, Ã_{t+1}J^(ℓ)_t on p.20 and S⁽¹⁾_{i+1:n}εᵢ in (50) → any finite ℝ^d-valued martingale difference sequence for any filtration; reason: each instance is a martingale difference sequence, for the forward filtration on p.20 and for the reversed filtration σ(Zᵢ,…,Zₙ) in (50)
--   - encoding: E^{1/p}[‖X‖^p] of a nonnegative or vector quantity → eLpNorm X (ENNReal.ofReal p) P in ℝ≥0∞; reason: same value, and an infinite moment would falsify the bound rather than make it vacuous
-- source:
--   Durmus, Moulines, Naumov & Samsonov, Finite-time High-probability Bounds for Polyak-Ruppert Averaged Iterates of Linear Stochastic Approximation, arXiv:2207.04475v2, (50), p.18; proof of Theorem 2, p.20 (Burkholder, Osekowski 2012, Theorem 8.6, with Minkowski)

import Mathlib
import Definitions.Def_PolyakJuditsky_Averaging_Model
import Definitions.Def_LSAPR_Model

open MeasureTheory ProbabilityTheory PolyakJuditsky.Averaging

namespace LSAPR

/-- The Burkholder inequality (Osekowski 2012, Theorem 8.6) combined with Minkowski's inequality,
as used in (50), arXiv:2207.04475v2, p.18 and on p.20: for an `ℝ^d`-valued martingale difference
sequence `D₀, …, D_{m-1}` with respect to a filtration `ℱ` (`D i` is `ℱ (i + 1)`-measurable and
`E[D i | ℱ i] = 0`) and real `p ≥ 2`,
`E^{1/p}[‖∑ D_i‖^p] ≤ p (∑ E^{2/p}[‖D_i‖^p])^{1/2}`.

**Formalization Note.** Stated for an arbitrary filtration: the paper applies it to the forward
filtration `F_t` on p.20 and, for the sequence `S^{(1)}_{i+1:n} ε_i` of (50), to the reversed
filtration `σ(Z_i, …, Z_n)`. A moment `E[‖D_i‖^p]` may be infinite: the right side is then `⊤`. -/
theorem burkholder_minkowski {d : ℕ} {Ω : Type*} {mΩ : MeasurableSpace Ω} (P : Measure Ω)
    [IsProbabilityMeasure P] (ℱ : Filtration ℕ mΩ) (m : ℕ) (D : ℕ → Ω → Vec d)
    (hadapted : ∀ i, i < m → StronglyMeasurable[ℱ (i + 1)] (D i))
    (hint : ∀ i, i < m → Integrable (D i) P)
    (hmds : ∀ i, i < m → P[D i | ℱ i] =ᵐ[P] 0)
    (p : ℝ) (hp : 2 ≤ p) :
    eLpNorm (fun ω => ∑ i ∈ Finset.range m, D i ω) (ENNReal.ofReal p) P ≤
      ENNReal.ofReal p *
        (∑ i ∈ Finset.range m, eLpNorm (D i) (ENNReal.ofReal p) P ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := by sorry

end LSAPR
