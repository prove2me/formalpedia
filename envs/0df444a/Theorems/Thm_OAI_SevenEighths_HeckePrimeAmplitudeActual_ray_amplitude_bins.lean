-- Prove2me | Theorems.Thm_OAI_SevenEighths_HeckePrimeAmplitudeActual_ray_amplitude_bins
-- name    : OAI.SevenEighths.HeckePrimeAmplitudeActual.ray_amplitude_bins
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-09T01:49:06.242865+00:00
-- url     : https://prove2.me/theorems/4df950f2-4e00-4afb-84a3-3dc363e1732e
-- title:
--   Amplitude bins of ray prime polynomials
-- statement:
--   Let $M\ne0$ be an ideal of $\mathcal O$, $H$ a subgroup of $(\mathcal O/M)^\times$ containing `RayOrthogonality.globalUnits M`, $W$ smooth with support in $[A,B]$, $A>0$, and reals $R\ge0$, $d_{\min}>0$, $d_{\max}\ge0$, $r_{\min}>0$, $\tau,\varepsilon>0$, $0<e<1/1000$, $\kappa>0$, $\eta\ge0$, `mesh` $>0$, $\sigma_{\min},\sigma_{\max}$ with $8eR+\kappa\le\varepsilon<r_{\min}\cdot\mathrm{mesh}$. Then for all sufficiently large $Z$: for every $d\in[d_{\min},d_{\max}]$ with $Z^d\ge2$ and $Z^\tau>2$, every `Character` $\chi$ all of whose twists `twistedFamily M H hH χ θ` have nontrivial residue character and modulus norm $\le Z^d$, every $a\in[51/100,1]$ and $i$ with `zeroMaximum (twistedFamily M H hH χ) _ (3(i+1)Z^τ)` $<a+2e$, every $r\in[r_{\min},R]$, $\sigma\in[\sigma_{\min},\sigma_{\max}]$ and `freq` with $|\mathrm{freq}|+Z^\tau/2\le(3i+2)Z^\tau$ and $(3+(3i+2)Z^\tau)^2\le(Z^d)^\eta$: with $Q=$`rayPrimePolynomial M H χ W B ((Z^d)^r) σ freq` and $g=$`amplitude ((Z^d)^r) (a-1/2) mesh Q`, we have $0\le g\le a-1/2$, $g\in$`labels (a-1/2) mesh`, $|Q|\le((Z^d)^r)^{g+\mathrm{mesh}}$, and if $g>0$ then $(Z^d)^{2rg}\le|Q|^2$.
--
--   Lean: `OAI.SevenEighths.HeckePrimeAmplitudeActual.ray_amplitude_bins` in `lean/OAI/NumberTheory/DirichletL/Hecke/PrimeAmplitudeActual.lean` (OpenAI); the definitions it uses are in the definitions bundles of this split (OpenAI's, carved) and in wurtle's bundle `HeckeSevenEighths`.
-- source:
--   OpenAI, The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re s > 7/8, OpenAI Math Release, September 30, 2026, family 003 of https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory/DirichletL

import Mathlib
import Definitions.Def_HeckeSevenEighths
import Definitions.Def_OAIHecke78B017

section

namespace OAI

noncomputable section
open Filter Set
open scoped Topology ContDiff
namespace SevenEighths.HeckePrimeAmplitudeActual
open HeckeFamily HeckePrimeRay HeckePrimeAmplitudeBins
variable (M : Ideal O) [NeZero M]
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

attribute [local instance] OAI.SevenEighths.HeckePrimeAmplitudeActual.instFiniteQuotientOIdeal
theorem ray_amplitude_bins (W : ℝ→ℂ) (A B : ℝ) (hA : 0<A)
    (hWs : Function.support W⊆Icc A B) (hW : ContDiff ℝ ∞ W)
    (R dmin dmax rmin τ ε e κ η mesh σmin σmax : ℝ)
    (hR : 0≤R) (hdmin : 0<dmin) (hdmax : 0≤dmax) (hrmin : 0< rmin)
    (hτ : 0<τ) (hε : 0<ε) (he : 0<e) (he' : e<1/1000)
    (hκ : 0<κ) (hη : 0≤η) (hmesh : 0< mesh)
    (hbudget : 8*e*R+κ≤ε) (hgap : ε< rmin*mesh) :
    ∀ᶠ Z : ℝ in atTop, ∀ d : ℝ, dmin≤d → d≤dmax → 2≤Z^d → 2<Z^τ →
    ∀ (χ : Character) (hχ : ∀ θ : RayQuotient.Characters M H,
      (twistedFamily M H hH χ θ).residue≠1) (a : ℝ) (i : ℕ),
      51/100≤a → a≤1 →
      HeckeDetectorZeros.zeroMaximum (twistedFamily M H hH χ) hχ (3*(i+1 : ℕ)*Z^τ)<a+2*e →
    ∀ r σ freq : ℝ, rmin≤ r → r≤R → σmin≤σ → σ≤σmax →
      (∀ θ : RayQuotient.Characters M H,(twistedFamily M H hH χ θ).modulus.absNorm≤Z^d) →
      |freq|+Z^τ/2≤(3*i+2 : ℕ)*Z^τ → (3+(3*i+2 : ℕ)*Z^τ)^2≤(Z^d)^η →
    let Q := rayPrimePolynomial M H χ W B ((Z^d)^r) σ freq
    let g := amplitude ((Z^d)^r) (a-1/2) mesh Q
    0≤g ∧ g≤a-1/2 ∧ g∈labels (a-1/2) mesh ∧
      ‖Q‖≤((Z^d)^r)^(g+mesh) ∧ (0<g → (Z^d)^(2*r*g)≤‖Q‖^2) := by
  sorry

end SevenEighths.HeckePrimeAmplitudeActual

end

end OAI
end
