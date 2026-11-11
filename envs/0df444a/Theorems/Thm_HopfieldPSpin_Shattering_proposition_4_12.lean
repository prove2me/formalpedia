-- Prove2me | Theorems.Thm_HopfieldPSpin_Shattering_proposition_4_12
-- name    : HopfieldPSpin.Shattering.proposition_4_12
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T19:09:37.93865+00:00
-- url     : https://prove2.me/theorems/bfa502a1-d011-47f5-8525-f1eebe13f9f7
-- title:
--   Proposition 4.12 — weighted soft distance gap $\mu_{n,\beta}(B_n)\le e^{-gn/4}$ with probability $\to1$
-- statement:
--   Fix $\alpha>0$, $p\ge3$, a storage sequence with (2.2), a pattern law, $0<\beta<\sqrt{2\log2}$, $\kappa>0$ and $0<r<R<1/2$. Assume, as §4.6 obtains from Theorems 4.10 and 4.9 for $p$ large, that $\frac1n\log Z_n(\beta)\to\log2+\beta^2/2$ in probability and that (4.24) holds uniformly over $\sigma,\tau$ and $|s|\le\beta+\kappa$. If $g=g_{p,\beta}(r,R)>0$ and $0<\beta\kappa<g/4$, then with probability tending to one
--   $$\mu_{n,\beta}(B_n)\le e^{-gn/4},\qquad B_n=\{\sigma\in W_n(\kappa):\exists\tau,\ H_n(\tau)\ge(\beta-\kappa)n,\ d_n(\sigma,\tau)\in[r,R]\}.$$
--
--   Differences from the source:
--   - encoding: spins $\sigma\in\{-1,1\}^n$, patterns $k=1,\dots,M$, coordinates $i=1,\dots,n$ → `Config n = Fin n → ℤˣ` (the units of ℤ are exactly ±1), patterns `Fin M`, coordinates `Fin n` (0-based); reason: Lean convention; the same configurations and indices
--   - generalization: §4.6 standing: $p$ large enough that Theorem 4.10 applies at β and Theorem 4.9 with $S=\beta+\kappa$ → any $p\ge3$, with hypotheses `FreeEnergyConverges p M law β` and `LaplaceTwo p M law (Icc (-(β+κ)) (β+κ))`; reason: these are exactly the facts the proof uses (the proof of Proposition 4.15 says so); for $p$ large Theorems 4.10 (via (4.43)) and 4.9 supply them, so the source's statement follows
--   - encoding: probability of the good event tends to 1 → the (outer) measure of the complementary event tends to 0; reason: equivalent for the measurable events of the paper; the complement form needs no measurability proof and is not weaker
-- source:
--   Kızıldağ, Şahin, Hopfield Model with p-spin Interactions: Shattering, Disorder Chaos and Sampling Hardness, STOC 2027 submission (manuscript sha256 4bbdc838…), p. 30 (PDF 32), Proposition 4.12, (4.46)–(4.47); §4.6 preamble p. 29 (PDF 31)

import Mathlib
import Definitions.Def_HopfieldPSpin_Shattering_Model
import Definitions.Def_HopfieldPSpin_Shattering_Entropy
import Definitions.Def_HopfieldPSpin_Shattering_Shattered

open MeasureTheory Filter Topology

namespace HopfieldPSpin.Shattering

/-- Proposition 4.12 (p. 30), in the hypothesis form of §4.6: for `0 < r < R < 1/2`, if
`n⁻¹ log Z_n(β) → f` in probability, (4.24) holds uniformly over `σ, τ` and `|s| ≤ β + κ`,
`g = g_{p,β}(r, R) > 0` and `0 < βκ < g/4`, then `µ_{n,β}(B_n) ≤ e^{−g n/4}` with probability
tending to one. -/
theorem proposition_4_12 (α : ℝ) (hα : 0 < α) (p : ℕ) (hp : 3 ≤ p) (M : ℕ → ℕ)
    (hM : StorageCondition p M α) (law : PatternLaw) (β : ℝ) (hβ0 : 0 < β)
    (hβ : β < Real.sqrt (2 * Real.log 2)) (κ : ℝ) (hκ : 0 < κ) (r R : ℝ) (hr : 0 < r)
    (hrR : r < R) (hR : R < 1 / 2)
    (hF : FreeEnergyConverges p M law β) (hL : LaplaceTwo p M law (Set.Icc (-(β + κ)) (β + κ)))
    (hg : 0 < gapG p β r R) (hβκ0 : 0 < β * κ) (hβκ : β * κ < gapG p β r R / 4) :
    Tendsto (fun n : ℕ => disorderLaw n (M n) law
        {η | Real.exp (-(gapG p β r R * n / 4)) <
          massOf (gibbs n (M n) p β η) (badSet n (M n) p β κ r R η)})
      atTop (𝓝 0) := by sorry

end HopfieldPSpin.Shattering
