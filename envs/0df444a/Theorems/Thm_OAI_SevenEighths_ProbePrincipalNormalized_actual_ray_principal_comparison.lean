-- Prove2me | Theorems.Thm_OAI_SevenEighths_ProbePrincipalNormalized_actual_ray_principal_comparison
-- name    : OAI.SevenEighths.ProbePrincipalNormalized.actual_ray_principal_comparison
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-09T02:23:02.544666+00:00
-- url     : https://prove2.me/theorems/249d7a03-e910-4cc4-9cac-a239d7701dc6
-- title:
--   Normalized principal row sums approximate the signal
-- statement:
--   Let $M\ne0$ with finite quotient, $H\supseteq$`globalUnits M`, $\eta$, $S$ with `SourceExclusions S`, $0<c\le d$, $B\ge0$, $\ell_{\min}>0$, injective $\ell_j\ge\ell_{\min}$ with $\sum\ell_j=1/6$, smooth compactly supported weights $W_j$ on $(c,d)$ with $0\le W_j\le B$, nonzero, and the further data of the Lean. Then there is $C>0$ such that eventually in $Z$ the normalizer (as in `actual_ray_normalizer_inverse`) is nonzero and
--   $$\Big\|\frac{\sum_P\prod_jW_j(N(P_j)/Z^{\ell_j})\,\texttt{principalRowIntegral}(\dots,Z^{17/48},Z^{23/48},Z)}{\mathrm{normer}}-\texttt{signal}(\eta_S)(\texttt{sourceCorrection}\,\eta\,S)(-11/16)\,Z\Big\|\le C\big(Z^{\beta-11/16-17/48000+\nu}+Z^{\beta-11/16+e-7\ell_{\min}/8}\big).$$
--
--   Lean: `OAI.SevenEighths.ProbePrincipalNormalized.actual_ray_principal_comparison` in `lean/OAI/NumberTheory/DirichletL/Detector/PrincipalNormalized.lean` (OpenAI); the definitions it uses are in the definitions bundles of this split (OpenAI's, carved) and in wurtle's bundle `HeckeSevenEighths`.
-- source:
--   OpenAI, The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re s > 7/8, OpenAI Math Release, September 30, 2026, family 003 of https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory/DirichletL

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_HeckeSevenEighths
import Definitions.Def_OAIHecke78B027

section

namespace OAI

noncomputable section
open scoped Classical BigOperators Topology ContDiff
open Complex Filter
namespace SevenEighths.ProbePrincipalNormalized
open HeckeFamily ProbePhysical CompletedGauss ProbeFiniteProductBounds
open PrincipalMellinResidues PrincipalSignalComparison ProbePrincipalResidueActual ProbeRaySlots
local notation "Id" => Ideal HeckeFamily.O

theorem actual_ray_principal_comparison {K : ℕ}
    (M : Id) [NeZero M] [Finite (HeckeFamily.O ⧸ M)]
    (H : Subgroup (HeckeFamily.O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)
    (η : Character) (S : Finset Id) (hS : SourceExclusions S)
    (c d B ellMin : ℝ) (hc : 0<c) (hd : c≤d) (hB : 0≤B) (hmin : 0<ellMin)
    (ell : Fin K→ℝ) (hell : ∀j,ellMin≤ell j) (hdis : Function.Injective ell)
    (hsum : (∑j,ell j)=1/6)
    (W : Fin K→ℝ→ℝ) (hW : ∀j,ContDiff ℝ ∞ (W j))
    (hcompact : ∀j,HasCompactSupport (W j))
    (hsupp : ∀j,Function.support (W j)⊆Set.Ioo c d)
    (hWbounds : ∀j y,0≤W j y ∧ W j y≤B) (hne : ∀j,W j≠0)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (hr0 : ∀y,(W0 y).im=0) (hr1 : ∀y,(W1 y).im=0)
    (hp0 : ∀y,0≤(W0 y).re) (hp1 : ∀y,0≤(W1 y).re) (hn0 : W0≠0) (hn1 : W1≠0)
    (e nu : ℝ) (he : 0<e) (hehi : e≤1/1000) (hnu : 0<nu)
    (ha : 7/8<HeckeZeroSupremum.beta+e) (ha2 : HeckeZeroSupremum.beta+e≤2) :
    letI : NeZero (∏p∈S,p) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
    ∃C : ℝ,0<C ∧ ∀ᶠZ : ℝ in atTop,
      let T := fun j=>pool (RayQuotient.identityClass M H) S c d (Z^(ell j))
      let normer := sourceResidueConstant W0 W1 (∏p∈S,p)*
        (Probe.principalScalar Finset.univ Z (1/6)
          (slotMass T (residueWeights W (fun j=>Z^(ell j)))) : ℂ)
      normer≠0 ∧
      ‖(∑P:(∀j,T j),(∏j,(W j ((Ideal.absNorm (P j).val.val:ℝ)/Z^(ell j)):ℂ))*
        principalRowIntegral η S (fun j=>primaryGenerator (P j).val.val)
          W0 W1 (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z)/normer-
        HeckeSignal.signal (η.excludePrimes S hS.prime) (sourceCorrection η S) (-11/16) Z‖≤
      C*(Z^(HeckeZeroSupremum.beta-11/16-17/48000+nu)+
        Z^(HeckeZeroSupremum.beta-11/16+e-(7/8)*ellMin)) := by
  sorry
end SevenEighths.ProbePrincipalNormalized
end

end OAI
end
