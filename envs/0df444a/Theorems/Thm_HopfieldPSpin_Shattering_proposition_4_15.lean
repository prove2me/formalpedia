-- Prove2me | Theorems.Thm_HopfieldPSpin_Shattering_proposition_4_15
-- name    : HopfieldPSpin.Shattering.proposition_4_15
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T19:09:47.858556+00:00
-- url     : https://prove2.me/theorems/25839997-0d64-420c-ac05-f83d24094315
-- title:
--   Proposition 4.15 — sufficient condition for $(r,R)$-shattering from free-energy convergence and the Laplace estimates
-- statement:
--   Fix $\alpha>0$, an integer $p\ge5$ and $\beta>0$; consider the model under (2.2) with either pattern law. Assume $\frac1n\log Z_n(\beta)\to f=\log2+\beta^2/2$ in probability and that (4.23)–(4.24) hold with $o(1)$ errors uniform over $\sigma,\tau\in\Sigma_n$ and $|s|\le2\beta$. Let $r,R$ be fixed with
--   $$0<2r<R<1/2,\qquad g_{p,\beta}(r,R)>0,\qquad h(r)<\log2-\frac{\beta^2}2 .$$
--   Then there are constants $c=(c_1,c_2,c_3)\in(0,\infty)^3$, independent of $n$ and of the disorder, such that $\mathbb P(S_n(r,R,c))\to1$, where $S_n(r,R,c)=\{\eta:\mu_{n,\beta}\text{ is }(r,R,c)\text{-shattered}\}$; in particular $(\mu_{n,\beta})_n$ is $(r,R)$-shattered (Definition 2.1(b)).
--
--   Differences from the source:
--   - encoding: spins $\sigma\in\{-1,1\}^n$, patterns $k=1,\dots,M$, coordinates $i=1,\dots,n$ → `Config n = Fin n → ℤˣ` (the units of ℤ are exactly ±1), patterns `Fin M`, coordinates `Fin n` (0-based); reason: Lean convention; the same configurations and indices
--   - encoding: (4.23)–(4.24) with $o(1)$ errors uniform over σ, τ and $|s|\le2\beta$ → `LaplaceOne` and `LaplaceTwo` on `Icc (-(2β)) (2β)`; reason: same hypothesis
--   - encoding: probability of the good event tends to 1 → the (outer) measure of the complementary event tends to 0; reason: equivalent for the measurable events of the paper; the complement form needs no measurability proof and is not weaker
-- source:
--   Kızıldağ, Şahin, Hopfield Model with p-spin Interactions: Shattering, Disorder Chaos and Sampling Hardness, STOC 2027 submission (manuscript sha256 4bbdc838…), p. 34 (PDF 36), Proposition 4.15

import Mathlib
import Definitions.Def_HopfieldPSpin_Shattering_Model
import Definitions.Def_HopfieldPSpin_Shattering_Entropy
import Definitions.Def_HopfieldPSpin_Shattering_Shattered

open MeasureTheory Filter Topology

namespace HopfieldPSpin.Shattering

/-- Proposition 4.15 (p. 34): sufficient condition for shattering. For `p ≥ 5`, `β > 0`,
(2.2) and either pattern law, if `n⁻¹ log Z_n(β) → log 2 + β²/2` in probability and
(4.23)–(4.24) hold with `o(1)` errors uniform over `σ, τ` and `|s| ≤ 2β`, then for fixed
`0 < 2r < R < 1/2` with `g_{p,β}(r, R) > 0` and `h(r) < log 2 − β²/2` there are
`c₁, c₂, c₃ > 0` with `P(S_n(r, R, c)) → 1`. -/
theorem proposition_4_15 (α : ℝ) (hα : 0 < α) (p : ℕ) (hp : 5 ≤ p) (β : ℝ) (hβ : 0 < β)
    (M : ℕ → ℕ) (hM : StorageCondition p M α) (law : PatternLaw)
    (hF : FreeEnergyConverges p M law β)
    (hL1 : LaplaceOne p M law (Set.Icc (-(2 * β)) (2 * β)))
    (hL2 : LaplaceTwo p M law (Set.Icc (-(2 * β)) (2 * β)))
    (r R : ℝ) (hr : 0 < 2 * r) (hrR : 2 * r < R) (hR : R < 1 / 2) (hg : 0 < gapG p β r R)
    (hh : Real.binEntropy r < Real.log 2 - β ^ 2 / 2) :
    ∃ c₁ c₂ c₃ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ 0 < c₃ ∧
      Tendsto (fun n : ℕ => disorderLaw n (M n) law
          {η | ¬ IsShattered n r R c₁ c₂ c₃ (gibbs n (M n) p β η)})
        atTop (𝓝 0) := by sorry

end HopfieldPSpin.Shattering
