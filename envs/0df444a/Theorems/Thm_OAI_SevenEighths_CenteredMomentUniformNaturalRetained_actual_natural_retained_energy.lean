-- Prove2me | Theorems.Thm_OAI_SevenEighths_CenteredMomentUniformNaturalRetained_actual_natural_retained_energy
-- name    : OAI.SevenEighths.CenteredMomentUniformNaturalRetained.actual_natural_retained_energy
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-09T02:04:27.47746+00:00
-- url     : https://prove2.me/theorems/1b12c112-1e31-455e-87ec-21babd8a3337
-- title:
--   Energy of the natural retained Schwartz sums
-- statement:
--   For $\epsilon>0$, $C_{\mathrm{scale}}>0$, $\xi>0$ and $B,J\in\mathbb N$ with $B\ge2$ there are a finite $H\subseteq\mathbb N\times\mathbb N$ and $C>0$ such that for all sufficiently large $Z$ ($Z>1$), every finite type $\iota$, Schwartz $G_i$, characters $\chi_i,\psi_i$ with $N(\psi_i.\mathrm{modulus})N(\texttt{redundantIdeal}\,\chi_i.\mathrm{modulus}\,\psi_i.\mathrm{modulus})\le N(\chi_i.\mathrm{modulus})\le\min(C_{\mathrm{scale}}Z^M,R_{\mathrm{cap}})$, $P_i\in\mathbb C$, $\omega_i$, a smooth $W_{\mathrm{short}}$ supported in $[c,d]$ ($d\ge0$), reals $M$, `along`, $b_{\mathrm{short}}$, $D>0$ bounding the $H$-seminorms of the $G_i$, $E\ge0$, $R_{\mathrm{cap}}\ge1$: if for all $v$, $j,k\in\mathrm{Fin}\,2$ and $x\in[0,\max(0,M-\mathrm{along}+\xi)\log Z]$
--   $$\sum_i\big\|\texttt{polynomial}\,\chi_i\,\mathrm{false}\,(\texttt{scaleTest annulus}\,j)\,e^x\,0\,(-2\pi v)\cdot\texttt{polynomial}\,\chi_i\,\mathrm{false}\,(\texttt{scaleTest}\,W_{\mathrm{short}}\,k)\,Z^{b_{\mathrm{short}}}\,0\,\omega_i\cdot P_i\big\|^2\le E(1+|v|)^{2J},$$
--   then $\sum_i\|\texttt{retainedSchwartz}\,\chi_i\,\psi_i\,G_i\,Z^{\mathrm{along}}\,Z^{\xi/4}\cdot\texttt{polynomial}\,\chi_i\,\mathrm{false}\,W_{\mathrm{short}}\,Z^{b_{\mathrm{short}}}\,0\,\omega_i\cdot P_i\|^2\le C R_{\mathrm{cap}}^{\epsilon}D^2\big(1+2\max(0,M-\mathrm{along}+\xi)\log Z\big)E$.
--
--   Lean: `OAI.SevenEighths.CenteredMomentUniformNaturalRetained.actual_natural_retained_energy` in `lean/OAI/NumberTheory/DirichletL/Moments/UniformNaturalRetained.lean` (OpenAI); the definitions it uses are in the definitions bundles of this split (OpenAI's, carved) and in wurtle's bundle `HeckeSevenEighths`.
-- source:
--   OpenAI, The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re s > 7/8, OpenAI Math Release, September 30, 2026, family 003 of https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory/DirichletL

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_HeckeSevenEighths
import Definitions.Def_OAIHecke78B019

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter
namespace SevenEighths.CenteredMomentUniformNaturalRetained
open HeckeFamily HeckeDyadic CenteredMomentScaleSupremum CenteredMomentNaturalPrimitive
open CenteredMomentUniformReflectionApproximation CenteredMomentRetainedWeightedSource
open CenteredMomentReflectionWeightedEnergy
open CenteredMomentOriginalReflectionApproximation CenteredMomentSectorLocalization

theorem actual_natural_retained_energy (epsilon Cscale xi : ℝ)
     (hepsilon : 0<epsilon) (hscale : 0<Cscale) (hxi : 0<xi)
    (B J : ℕ) (hB : 2≤B) :
    ∃H : Finset (ℕ×ℕ),∃C : ℝ,0<C ∧ ∀ᶠ Z : ℝ in atTop,1<Z ∧
      ∀{ι : Type}[Fintype ι],∀(G : ι→𝓢(ℝ,ℂ))(χ ψ : ι→Character)(P : ι→ℂ)(omega : ι→ℝ)
        (Wshort : ℝ→ℂ)(c d M along bshort D E Rcap : ℝ),
      0≤d → Function.support Wshort⊆Set.Icc c d → ContDiff ℝ ∞ Wshort →
      (∀i,(ψ i).modulus.absNorm*(redundantIdeal (χ i).modulus (ψ i).modulus).absNorm≤(χ i).modulus.absNorm) →
      (∀i,((χ i).modulus.absNorm:ℝ)≤Cscale*Z^M) →
      0<D → 0≤E → (∀i,H.sup (schwartzSeminormFamily ℝ ℝ ℂ) (G i)≤D) → 1≤Rcap →
      (∀i,((χ i).modulus.absNorm:ℝ)≤Rcap) →
      (∀v : ℝ,∀j k : Fin 2,∀x∈Set.Icc 0 (max 0 (M-along+xi)*Real.log Z),
        (∑i,‖polynomial (χ i) false (scaleTest (fun z : ℝ=>(annulus z:ℂ)) j)
          (Real.exp x) 0 (-2*Real.pi*v)*
          polynomial (χ i) false (scaleTest Wshort k) (Z^bshort) 0 (omega i)*P i‖^2)
          ≤E*(1+‖v‖)^(2*J)) →
      (∑i,‖retainedSchwartz (χ i) (ψ i) (G i) (Z^along) (Z^(xi/4))*
        polynomial (χ i) false Wshort (Z^bshort) 0 (omega i)*P i‖^2)≤
        C*Rcap^epsilon*D^2*(1+2*(max 0 (M-along+xi)*Real.log Z))*E := by
  sorry

end SevenEighths.CenteredMomentUniformNaturalRetained

end

end OAI
end
