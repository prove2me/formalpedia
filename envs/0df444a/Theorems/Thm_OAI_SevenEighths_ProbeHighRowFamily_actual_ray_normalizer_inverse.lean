-- Prove2me | Theorems.Thm_OAI_SevenEighths_ProbeHighRowFamily_actual_ray_normalizer_inverse
-- name    : OAI.SevenEighths.ProbeHighRowFamily.actual_ray_normalizer_inverse
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-09T02:07:26.878981+00:00
-- url     : https://prove2.me/theorems/b88c0824-c8a5-437a-98c9-2f5e049b136e
-- title:
--   The principal residue normalizer is invertible with polynomial bound
-- statement:
--   Let $M\ne0$ be an ideal of $\mathcal O$ with finite quotient, $H\supseteq$`globalUnits M`, $S$ with `SourceExclusions S`, $0<c\le b$, weights $\ell_j>0$ ($j<K$) with $\sum\ell_j=1/6$, nonnegative nonzero smooth compactly supported $W_j$ supported in $(c,b)$, real nonnegative nonzero Schwartz $W_0,W_1$ supported in $[a_0,b_0]$, $[a_1,b_1]$ ($a_0,a_1>0$), and $\nu>0$. Then there is $C>0$ such that for all sufficiently large $Z$, with $T_j=$`pool (identityClass M H) S c b (Z^{ℓ_j})` and normalizer $N_Z=$`sourceResidueConstant W0 W1 (∏S)`·`Probe.principalScalar univ Z (1/6) (slotMass T (residueWeights W (Z^ℓ)))`, we have $N_Z\ne0$ and $|N_Z^{-1}|\le CZ^\nu$.
--
--   Lean: `OAI.SevenEighths.ProbeHighRowFamily.actual_ray_normalizer_inverse` in `lean/OAI/NumberTheory/DirichletL/PrimeRows/CubeNormalizer.lean` (OpenAI); the definitions it uses are in the definitions bundles of this split (OpenAI's, carved) and in wurtle's bundle `HeckeSevenEighths`.
-- source:
--   OpenAI, The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re s > 7/8, OpenAI Math Release, September 30, 2026, family 003 of https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory/DirichletL

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_HeckeSevenEighths
import Definitions.Def_OAIHecke78B022

section

namespace OAI

noncomputable section
open scoped Classical BigOperators Topology ContDiff
open Filter
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily ProbePhysical ProbeRaySlots PrincipalSignalComparison
open PrincipalMellinResidues ProbePrincipalResidueActual
local notation "O" => HeckeFamily.O

theorem actual_ray_normalizer_inverse {K : ℕ}
    (M : Ideal O) [NeZero M] [Finite (O ⧸ M)]
    (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)
    (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (c b : ℝ) (hc : 0<c) (hcb : c≤b)
    (ell : Fin K→ℝ) (hell : ∀j,0<ell j) (hellsum : ∑j,ell j=1/6)
    (W : Fin K→ℝ→ℝ) (hW : ∀j,ContDiff ℝ ∞ (W j)) (hcompact : ∀j,HasCompactSupport (W j))
    (hsupp : ∀j,Function.support (W j)⊆Set.Ioo c b) (hp : ∀j y,0≤W j y) (hne : ∀j,W j≠0)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (hr0 : ∀y,(W0 y).im=0) (hr1 : ∀y,(W1 y).im=0)
    (hp0 : ∀y,0≤(W0 y).re) (hp1 : ∀y,0≤(W1 y).re) (hn0 : W0≠0) (hn1 : W1≠0)
    (nu : ℝ) (hnu : 0<nu) :
    letI : NeZero (∏P∈S,P) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
    ∃C : ℝ,0<C ∧ ∀ᶠZ : ℝ in atTop,
      let T := fun j=>pool (RayQuotient.identityClass M H) S c b (Z^(ell j))
      let normer := sourceResidueConstant W0 W1 (∏P∈S,P)*
        (Probe.principalScalar Finset.univ Z (1/6)
          (slotMass T (residueWeights W (fun j=>Z^(ell j)))) : ℂ)
      normer≠0 ∧ ‖normer⁻¹‖≤C*Z^nu := by
  sorry

end SevenEighths.ProbeHighRowFamily

end

end OAI
end
