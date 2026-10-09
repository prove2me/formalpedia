-- Prove2me | Theorems.Thm_OAI_SevenEighths_CenteredMomentUniformRadialComparison_actual_original_radial_comparison
-- name    : OAI.SevenEighths.CenteredMomentUniformRadialComparison.actual_original_radial_comparison
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-09T01:43:25.975953+00:00
-- url     : https://prove2.me/theorems/7d172628-11fe-4a87-bc36-aabf1d8f074e
-- title:
--   Radial energy comparison for the original long polynomial
-- statement:
--   For reals $\epsilon>0$, $C_{\mathrm{scale}}>0$, $\xi>0$, `saving`, $L$ and $B,J\in\mathbb N$ with $B\ge2$, there are a finite $H\subseteq\mathbb N\times\mathbb N$ and $C,D>0$ such that for all sufficiently large $Z$ ($Z>1$) and all families over $z\in\mathcal O$ — Schwartz $G_z$, characters $\chi_z$ with nontrivial residue for kept $z$, $|P_z|\le P_{\mathrm{bound}}$, $\omega_z$, a predicate `keep` — with a Schwartz $\Phi$ ($\operatorname{Re}\Phi(\|\texttt{eisEmbedding}\,z\|^2/K)\ge0$, $K>0$), a smooth $W_{\mathrm{short}}$ supported in $[c,d]$, $d\ge0$, reals $M\le L+\mathrm{along}$, $E\ge0$, $\mathrm{Src}>0$ bounding the $H$-seminorms of $G_z$, $R_{\mathrm{cap}}\ge1$, $b_{\mathrm{short}}$, and modulus norms of kept $\chi_z$ at most $\min(C_{\mathrm{scale}}Z^M,R_{\mathrm{cap}})$: if for all $v$, $j,k\in\mathrm{Fin}\,2$ and $x\in[0,\max(0,M-\mathrm{along}+\xi)\log Z]$ the `radialEnergy` of the products of `polynomial` at the annulus test `scaleTest annulus j` (height $e^x$, frequency $-2\pi v$) and at `scaleTest Wshort k` (height $Z^{b_{\mathrm{short}}}$) with $P$ is at most $E(1+|v|)^{2J}$, then the `radialEnergy` of $z\mapsto$`polynomial χ_z false G_z (Z^along) 0 0`·`polynomial χ_z false Wshort (Z^bshort) 0 ω_z`·$P_z$ is at most
--   $$C R_{\mathrm{cap}}^{\epsilon}\mathrm{Src}^2\big(1+2\max(0,M-\mathrm{along}+\xi)\log Z\big)E+D R_{\mathrm{cap}}^{2\epsilon}\mathrm{Src}^2Z^{-2\,\mathrm{saving}}\,\texttt{radialEnergy}(z\mapsto\texttt{polynomial}\,\chi_z\,\mathrm{false}\,W_{\mathrm{short}}\,Z^{b_{\mathrm{short}}}\,0\,\omega_z\cdot P_z),$$
--   all energies over `keep` with $\Phi$, $K$.
--
--   Lean: `OAI.SevenEighths.CenteredMomentUniformRadialComparison.actual_original_radial_comparison` in `lean/OAI/NumberTheory/DirichletL/Moments/UniformRadialComparison.lean` (OpenAI); the definitions it uses are in the definitions bundles of this split (OpenAI's, carved) and in wurtle's bundle `HeckeSevenEighths`.
-- source:
--   OpenAI, The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re s > 7/8, OpenAI Math Release, September 30, 2026, family 003 of https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory/DirichletL

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_HeckeSevenEighths
import Definitions.Def_OAIHecke78B017

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter
namespace SevenEighths.CenteredMomentUniformRadialComparison
open HeckeFamily HeckeDyadic ConcreteTraceCRT
open CenteredMomentScaleSupremum CenteredMomentSectorLocalization
open CenteredMomentOriginalRadialComparison
local notation "O" => HeckeFamily.O

theorem actual_original_radial_comparison (epsilon Cscale xi saving L : ℝ)
     (hepsilon : 0<epsilon) (hscale : 0<Cscale) (hxi : 0<xi)
    (B J : ℕ) (hB : 2≤B) :
    ∃H : Finset (ℕ×ℕ),∃C D : ℝ,0<C ∧ 0<D ∧ ∀ᶠ Z : ℝ in atTop,1<Z ∧
      ∀(G:O→𝓢(ℝ,ℂ))(χ : O→Character)(P : O→ℂ)(omega : O→ℝ)(keep : O→Prop)
        (Φ : 𝓢(ℝ,ℂ))(K Pbound : ℝ)(Wshort : ℝ→ℂ)(c d M along bshort E Src Rcap : ℝ),
      0<K → (∀z,0≤(Φ (‖eisEmbedding z‖^2/K)).re) → (∀z,‖P z‖≤Pbound) →
      (∀z,keep z → (χ z).residue≠1) →
      0≤d → Function.support Wshort⊆Set.Icc c d → ContDiff ℝ ∞ Wshort →
      M≤L+along → (∀z,keep z → ((χ z).modulus.absNorm:ℝ)≤Cscale*Z^M) →
      0≤E → 0<Src → (∀z,keep z → H.sup (schwartzSeminormFamily ℝ ℝ ℂ) (G z)≤Src) → 1≤Rcap →
      (∀z,keep z → ((χ z).modulus.absNorm:ℝ)≤Rcap) →
      (∀v : ℝ,∀j k : Fin 2,∀x∈Set.Icc 0 (max 0 (M-along+xi)*Real.log Z),
        radialEnergy (fun z=>polynomial (χ z) false (scaleTest (fun y : ℝ=>(annulus y:ℂ)) j)
          (Real.exp x) 0 (-2*Real.pi*v)*
          polynomial (χ z) false (scaleTest Wshort k) (Z^bshort) 0 (omega z)*P z) keep Φ K
          ≤E*(1+‖v‖)^(2*J)) →
      radialEnergy (fun z=>polynomial (χ z) false (G z) (Z^along) 0 0*
        polynomial (χ z) false Wshort (Z^bshort) 0 (omega z)*P z) keep Φ K≤
        C*Rcap^epsilon*Src^2*(1+2*(max 0 (M-along+xi)*Real.log Z))*E+
        D*Rcap^(2*epsilon)*Src^2*Z^(-2*saving)*
          radialEnergy (fun z=>polynomial (χ z) false Wshort (Z^bshort) 0 (omega z)*P z) keep Φ K := by
  sorry

end SevenEighths.CenteredMomentUniformRadialComparison

end

end OAI
end
