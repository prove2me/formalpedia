-- Prove2me | Theorems.Thm_HopfieldPSpin_Shattering_proposition_4_11
-- name    : HopfieldPSpin.Shattering.proposition_4_11
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T19:09:39.171389+00:00
-- url     : https://prove2.me/theorems/47784607-e4ca-43c6-bf32-2ff3f790eee1
-- title:
--   Proposition 4.11 — energy localization $\mu_{n,\beta}(W_n(\kappa)^c)\le e^{-\kappa^2n/8}$ with probability $\to1$
-- statement:
--   Fix $\alpha>0$, $p\ge3$, a storage sequence with (2.2), a pattern law, $0<\beta<\sqrt{2\log2}$ and $\kappa>0$. Assume, as §4.6 obtains from Theorems 4.10 and 4.9 for $p$ large, that $\frac1n\log Z_n(\beta)\to f=\log2+\beta^2/2$ in probability and that (4.23) holds (uniformly in $\sigma$) at $s=\beta-\kappa$ and $s=\beta+\kappa$. Then
--   $$\mathbb P_{n,\eta}\big[\mu_{n,\beta}(W_n(\kappa)^c)\le e^{-\kappa^2n/8}\big]\to1,\qquad W_n(\kappa)=\{\sigma:|H_n(\sigma)/n-\beta|\le\kappa\}.$$
--   Almost all Gibbs mass lies in the energy window.
--
--   Differences from the source:
--   - encoding: spins $\sigma\in\{-1,1\}^n$, patterns $k=1,\dots,M$, coordinates $i=1,\dots,n$ → `Config n = Fin n → ℤˣ` (the units of ℤ are exactly ±1), patterns `Fin M`, coordinates `Fin n` (0-based); reason: Lean convention; the same configurations and indices
--   - generalization: §4.6 standing: $p$ large enough that Theorem 4.10 applies at β and Theorem 4.9 with $S=\beta+\kappa$; Proposition 4.11's hypothesis '(4.23) holds at β − κ and β + κ' → any $p\ge3$, with hypotheses `FreeEnergyConverges p M law β` and `LaplaceOne p M law {β - κ, β + κ}`; reason: these are exactly the facts the proof uses (the proof of Proposition 4.15 says so); for $p$ large Theorems 4.10 (via (4.43)) and 4.9 supply them, so the source's statement follows
--   - encoding: probability of the good event tends to 1 → the (outer) measure of the complementary event tends to 0; reason: equivalent for the measurable events of the paper; the complement form needs no measurability proof and is not weaker
-- source:
--   Kızıldağ, Şahin, Hopfield Model with p-spin Interactions: Shattering, Disorder Chaos and Sampling Hardness, STOC 2027 submission (manuscript sha256 4bbdc838…), p. 29 (PDF 31), §4.6 preamble and Proposition 4.11, (4.44)

import Mathlib
import Definitions.Def_HopfieldPSpin_Shattering_Model
import Definitions.Def_HopfieldPSpin_Shattering_Shattered

open MeasureTheory Filter Topology

namespace HopfieldPSpin.Shattering

/-- Proposition 4.11 (p. 29), in the hypothesis form of §4.6: if `n⁻¹ log Z_n(β) → f` in
probability and (4.23) holds (uniformly in `σ`) at `s = β − κ` and `s = β + κ`, then
`P[µ_{n,β}(W_n(κ)ᶜ) ≤ e^{−κ² n/8}] → 1`. -/
theorem proposition_4_11 (α : ℝ) (hα : 0 < α) (p : ℕ) (hp : 3 ≤ p) (M : ℕ → ℕ)
    (hM : StorageCondition p M α) (law : PatternLaw) (β : ℝ) (hβ0 : 0 < β)
    (hβ : β < Real.sqrt (2 * Real.log 2)) (κ : ℝ) (hκ : 0 < κ)
    (hF : FreeEnergyConverges p M law β) (hL : LaplaceOne p M law {β - κ, β + κ}) :
    Tendsto (fun n : ℕ => disorderLaw n (M n) law
        {η | Real.exp (-(κ ^ 2 * n / 8)) <
          massOf (gibbs n (M n) p β η) (Finset.univ \ energyWindow n (M n) p β κ η)})
      atTop (𝓝 0) := by sorry

end HopfieldPSpin.Shattering
