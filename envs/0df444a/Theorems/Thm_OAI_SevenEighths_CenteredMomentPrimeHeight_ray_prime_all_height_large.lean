-- Prove2me | Theorems.Thm_OAI_SevenEighths_CenteredMomentPrimeHeight_ray_prime_all_height_large
-- name    : OAI.SevenEighths.CenteredMomentPrimeHeight.ray_prime_all_height_large
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-09T01:47:04.890532+00:00
-- url     : https://prove2.me/theorems/aa1c8a1e-378a-4682-945a-7864097c728e
-- title:
--   Square bound for ray prime polynomials at large height
-- statement:
--   Let $M\ne0$ be an ideal of $\mathcal O$ (`HeckeFamily.O`), $H$ a subgroup of $(\mathcal O/M)^\times$ containing `RayOrthogonality.globalUnits M`, $W$ smooth with support in $[A,B]$, $A>0$, and reals $L_{\mathrm{mod}}\ge0$, $L_{\mathrm{slot}}\ge0$, `loss` $>0$, $lo,hi$, and $\kappa\ge2\beta-1$ where $\beta\ge51/100$ is OpenAI's constant `beta`. Then there are $C>0$, $Z_0>1$ such that for all $Z\ge Z_0$, $1\le P\le Z^{L_{\mathrm{slot}}}$, every `Character` $\chi$ with $N(\chi.\mathrm{modulus})\le Z^{L_{\mathrm{mod}}}$ all of whose twists `twistedFamily M H hH χ θ` ($\theta$ a ray class character) have nontrivial residue character, and all $\sigma\in[lo,hi]$ and `freq` with $2(|\log A|+|\log B|)+1\le\log P$:
--   $$\|\texttt{rayPrimePolynomial}\,M\,H\,\chi\,W\,B\,P\,\sigma\,\mathrm{freq}\|^2\le C\,P^{\kappa}Z^{\mathrm{loss}}(3+|\mathrm{freq}|)^{\mathrm{loss}}.$$
--
--   Lean: `OAI.SevenEighths.CenteredMomentPrimeHeight.ray_prime_all_height_large` in `lean/OAI/NumberTheory/DirichletL/Moments/PrimeHeight.lean` (OpenAI); the definitions it uses are in the definitions bundles of this split (OpenAI's, carved) and in wurtle's bundle `HeckeSevenEighths`.
-- source:
--   OpenAI, The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re s > 7/8, OpenAI Math Release, September 30, 2026, family 003 of https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory/DirichletL

import Mathlib
import Definitions.Def_HeckeSevenEighths
import Definitions.Def_OAIHecke78B017

section

namespace OAI

noncomputable section
open scoped Classical BigOperators ContDiff
open Set
namespace SevenEighths.CenteredMomentPrimeHeight
open HeckeFamily HeckePrimeRay HeckePrimeAnnular HeckeDyadic HeckeZeroSupremum
local notation "O" => HeckeFamily.O

variable (M : Ideal O) [NeZero M]
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

attribute [local instance] OAI.SevenEighths.CenteredMomentPrimeHeight.instFiniteQuotientOIdeal
theorem ray_prime_all_height_large (W : ℝ→ℂ) (A B : ℝ) (hA : 0<A)
    (hWs : Function.support W⊆Icc A B) (hW : ContDiff ℝ ∞ W)
    (Lmod Lslot loss lo hi κ : ℝ) (hLm : 0≤Lmod) (_hLs : 0≤Lslot) (hloss : 0<loss)
    (hbeta : (51/100:ℝ)≤beta) (hκ : 2*beta-1≤κ) :
    ∃C Z₀ : ℝ,0<C ∧ 1<Z₀ ∧ ∀ Z P : ℝ,Z₀≤Z → 1≤P → P≤Z^Lslot →
    ∀χ : Character,(χ.modulus.absNorm:ℝ)≤Z^Lmod →
      (∀θ : RayQuotient.Characters M H,(twistedFamily M H hH χ θ).residue≠1) →
    ∀σ freq : ℝ,lo≤σ → σ≤hi →
      2*(|Real.log A|+|Real.log B|)+1≤Real.log P →
      ‖rayPrimePolynomial M H χ W B P σ freq‖^2≤C*P^κ*Z^loss*(3+|freq|)^loss := by
  sorry

end SevenEighths.CenteredMomentPrimeHeight
end

end OAI
end
