-- Prove2me | Theorems.Thm_OAI_SevenEighths_HeckeDetectorDyadicActual_simultaneous_upper
-- name    : OAI.SevenEighths.HeckeDetectorDyadicActual.simultaneous_upper
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-09T01:46:36.460975+00:00
-- url     : https://prove2.me/theorems/ba4ded5d-4739-445c-8ed4-96ae807381cd
-- title:
--   Simultaneous upper bounds for inverse and plain dyadic polynomials
-- statement:
--   Let $R,d_{\max},\eta\ge0$, $\tau,\varepsilon>0$, $0<e<1/1000$, $0<\kappa\le1$ with $12e(R+2)+8\kappa+2\eta\le\varepsilon$. Then there is $C>0$ such that for all reals $Z\ge1$, $0\le d\le d_{\max}$ with $Z^\tau>2$, every finite family of characters $\chi_j$ with nontrivial residue characters, every $a\in[51/100,1]$ and $i\in\mathbb N$ with `HeckeDetectorZeros.zeroMaximum χ hχ (3(i+1)Z^τ)` $<a+2e$, and every $j$ and reals $D^*>0$, $0\le r,m\le R$, $\sigma\in[51/100,1]$, `freq` with $N(\chi_j.\mathrm{modulus})\le Z^d$, $(Z^d)^r\le4D^*$, $|\mathrm{freq}|+Z^\tau/2\le(3i+2)Z^\tau$ and $(3+(3i+2)Z^\tau)^4\le(Z^d)^\eta$: the square of the norm of `polynomial (χ j) true (inverseProfile cutoff positiveAnnular D* ((Z^d)^r)) ((Z^d)^r) σ freq` is at most $C(Z^d)^{(2a-1)r+\varepsilon}$, and the square of the norm of `polynomial (χ j) false positiveAnnular ((Z^d)^m) σ freq` is at most $C(Z^d)^{(2a-1)\min(m,1-m)+\varepsilon}$.
--
--   Lean: `OAI.SevenEighths.HeckeDetectorDyadicActual.simultaneous_upper` in `lean/OAI/NumberTheory/DirichletL/Hecke/DetectorDyadicActual.lean` (OpenAI); the definitions it uses are in the definitions bundles of this split (OpenAI's, carved) and in wurtle's bundle `HeckeSevenEighths`.
-- source:
--   OpenAI, The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re s > 7/8, OpenAI Math Release, September 30, 2026, family 003 of https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory/DirichletL

import Mathlib
import Definitions.Def_HeckeSevenEighths
import Definitions.Def_OAIHecke78B016

section

namespace OAI

noncomputable section

open scoped Classical ContDiff
open Set
namespace SevenEighths.HeckeDetectorDyadicActual
open HeckeFamily HeckeDyadic HeckeDetectorDyadicProfiles HeckeDetectorProfiles

theorem simultaneous_upper (R dmax τ ε e κ η : ℝ)
    (hR : 0≤R) (hdmax : 0≤dmax) (hτ : 0<τ) (hε : 0<ε)
    (he : 0<e) (he' : e<1/1000) (hκ : 0<κ) (hκ' : κ≤1) (hη : 0≤η)
    (hbudget : 12*e*(R+2)+8*κ+2*η≤ε) :
    ∃ C : ℝ, 0<C ∧ ∀ Z d : ℝ, 1≤Z → 0≤d → d≤dmax → 2<Z^τ →
      ∀ {ι : Type*} [Fintype ι] (χ : ι→Character)
        (hχ : ∀ j, (χ j).residue≠1) (a : ℝ) (i : ℕ),
        51/100≤a → a≤1 →
        HeckeDetectorZeros.zeroMaximum χ hχ (3*(i+1 : ℕ)*(Z^τ))<a+2*e →
        ∀ j : ι, ∀ Dstar r m σ freq : ℝ,
        (χ j).modulus.absNorm≤Z^d → 0<Dstar →
        0≤ r → r≤R → 0≤ m → m≤R → (Z^d)^r≤4*Dstar →
        51/100≤σ → σ≤1 → |freq|+(Z^τ)/2≤(3*i+2 : ℕ)*(Z^τ) →
        (3+(3*i+2 : ℕ)*(Z^τ))^4≤(Z^d)^η →
        ‖polynomial (χ j) true
          (HeckeDetectorDyadicBridge.inverseProfile cutoff positiveAnnular Dstar ((Z^d)^r))
          ((Z^d)^r) σ freq‖^2≤C*(Z^d)^((2*a-1)*r+ε) ∧
        ‖polynomial (χ j) false positiveAnnular ((Z^d)^m) σ freq‖^2≤
          C*(Z^d)^((2*a-1)*min m (1-m)+ε) := by
  sorry

end SevenEighths.HeckeDetectorDyadicActual

end

end OAI
end
