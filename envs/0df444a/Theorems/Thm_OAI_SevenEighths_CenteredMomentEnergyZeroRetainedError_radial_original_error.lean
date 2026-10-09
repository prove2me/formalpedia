-- Prove2me | Theorems.Thm_OAI_SevenEighths_CenteredMomentEnergyZeroRetainedError_radial_original_error
-- name    : OAI.SevenEighths.CenteredMomentEnergyZeroRetainedError.radial_original_error
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-09T01:41:53.996408+00:00
-- url     : https://prove2.me/theorems/70f7c697-9ff9-449e-8393-686c856b030c
-- title:
--   Radial energy of the original error term
-- statement:
--   For reals $\xi>0$, `saving`, $C_{\mathrm{scale}}>0$ and $\epsilon>0$ there are a finite $H\subseteq\mathbb N\times\mathbb N$ and $C>0$, $Z_0>1$ such that for all families indexed by $z\in\mathcal O$ (here `HeckeFamily.O`) — Schwartz functions $G(z)$, characters $\chi(z)$ (`Character`), $P(z)\in\mathbb C$ with $|P|\le P_{\mathrm{bound}}$, $\omega(z)\in\mathbb R$ and a predicate `keep` — a Schwartz $\Phi$ with $\operatorname{Re}\Phi(\|\texttt{eisEmbedding}\,z\|^2/K)\ge0$, $K>0$, $W_{\mathrm{short}}$ supported in $[c,d]$ with $d\ge0$, and reals $Z\ge Z_0$, $M$, `along` $>M+\xi$, $X_{\mathrm{short}}>0$, $\mathrm{Src}>0$, $R_{\mathrm{cap}}\ge1$, such that for kept $z$ the residue of $\chi(z)$ is nontrivial, the $H$-seminorms of $G(z)$ are at most Src and the modulus norm of $\chi(z)$ is at most $\min(C_{\mathrm{scale}}Z^M,R_{\mathrm{cap}})$:
--   $$\texttt{radialEnergy}\big(z\mapsto\texttt{polynomial}\,\chi_z\,\mathrm{false}\,G_z\,Z^{\mathrm{along}}\,0\,0\cdot\texttt{polynomial}\,\chi_z\,\mathrm{false}\,W_{\mathrm{short}}\,X_{\mathrm{short}}\,0\,\omega_z\cdot P_z\big)\le C R_{\mathrm{cap}}^{2\epsilon}\mathrm{Src}^2Z^{-2\,\mathrm{saving}}\,\texttt{radialEnergy}\big(z\mapsto\texttt{polynomial}\,\chi_z\,\mathrm{false}\,W_{\mathrm{short}}\,X_{\mathrm{short}}\,0\,\omega_z\cdot P_z\big),$$
--   both energies taken over `keep` with $\Phi$ and $K$.
--
--   Lean: `OAI.SevenEighths.CenteredMomentEnergyZeroRetainedError.radial_original_error` in `lean/OAI/NumberTheory/DirichletL/Energy/ZeroRetainedError.lean` (OpenAI); the definitions it uses are in the definitions bundles of this split (OpenAI's, carved) and in wurtle's bundle `HeckeSevenEighths`.
-- source:
--   OpenAI, The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re s > 7/8, OpenAI Math Release, September 30, 2026, family 003 of https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory/DirichletL

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_HeckeSevenEighths
import Definitions.Def_OAIHecke78B016

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentEnergyZeroRetainedError
open HeckeFamily HeckeDyadic ConcreteTraceCRT
open CenteredMomentNaturalPrimitive
open CenteredMomentOriginalRadialComparison
open CenteredMomentNaturalRowSource CenteredMomentFiniteProfileExceptional CenteredMomentLattice
local notation "O" => HeckeFamily.O

theorem radial_original_error (xi saving Cscale epsilon : ℝ)
    (hxi : 0<xi)(hscale : 0<Cscale)(hepsilon : 0<epsilon) :
    ∃H : Finset (ℕ×ℕ),∃C Z₀ : ℝ,0<C ∧ 1<Z₀ ∧
      ∀(G:O→𝓢(ℝ,ℂ))(χ:O→Character)(P:O→ℂ)(omega:O→ℝ)
        (keep:O→Prop)(Φ:𝓢(ℝ,ℂ))(K Pbound:ℝ)(Wshort:ℝ→ℂ)
        (c d Z M along Xshort Src Rcap:ℝ),
      Z₀≤Z → 0<K → (∀z,0≤(Φ (‖eisEmbedding z‖^2/K)).re) →
      (∀z,‖P z‖≤Pbound) → (∀z,keep z → (χ z).residue≠1) →
      0≤d → Function.support Wshort⊆Set.Icc c d → 0<Xshort →
      M+xi<along → 0<Src → 1≤Rcap →
      (∀z,keep z → H.sup (schwartzSeminormFamily ℝ ℝ ℂ) (G z)≤Src) →
      (∀z,keep z → ((χ z).modulus.absNorm:ℝ)≤Cscale*Z^M) →
      (∀z,keep z → ((χ z).modulus.absNorm:ℝ)≤Rcap) →
      radialEnergy (fun z=>polynomial (χ z) false (G z) (Z^along) 0 0*
        polynomial (χ z) false Wshort Xshort 0 (omega z)*P z) keep Φ K≤
        C*Rcap^(2*epsilon)*Src^2*Z^(-2*saving)*
          radialEnergy (fun z=>polynomial (χ z) false Wshort Xshort 0 (omega z)*P z) keep Φ K := by
  sorry

end SevenEighths.CenteredMomentEnergyZeroRetainedError

end

end OAI
end
