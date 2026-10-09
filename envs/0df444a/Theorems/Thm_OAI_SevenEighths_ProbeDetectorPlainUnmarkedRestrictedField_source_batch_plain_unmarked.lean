-- Prove2me | Theorems.Thm_OAI_SevenEighths_ProbeDetectorPlainUnmarkedRestrictedField_source_batch_plain_unmarked
-- name    : OAI.SevenEighths.ProbeDetectorPlainUnmarkedRestrictedField.source_batch_plain_unmarked
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-09T02:19:56.292299+00:00
-- url     : https://prove2.me/theorems/7f724a41-aa53-456c-8bef-f5256adfb374
-- title:
--   Plain unmarked fiber energies of source batches
-- statement:
--   Let $S$ be `SourceData` over `HighData` $D$ and assume a degree and control set such that for every $\eta_0$ the zero-stage bound `ZeroAt (internalQ (sourceFixedIdeal S) η₀) (1/4) (9/4) radialSupportUpper 0 1 2 (D.t/4) U degree control A` holds eventually in $U$. Then there is $J_{\mathrm{height}}$ such that for every `Character` $\eta$ there is $C>0$ with: eventually in $Z$, for every source batch fiber $F$ and the data of the Lean, with value $=\sum_{u}\|\texttt{polynomial}(\dots)(\texttt{logProfile}^{[j]}\dots)\cdot\texttt{polynomial}(\dots)(\texttt{logProfile}^{[k]}\dots)\|^2$ ($j+k\le2$, $\sigma\in[0,1]$, $|t|\le\mathrm{height}$): value $\le C(1+\mathrm{height})^{J_{\mathrm{height}}}(Z^d)^{\max(1,2F.m)+D.t}$ and value $\le C(1+\mathrm{height})^{J_{\mathrm{height}}}\max(Z^d,(Z^d)^{2F.m})(Z^d)^{D.t}$.
--
--   Lean: `OAI.SevenEighths.ProbeDetectorPlainUnmarkedRestrictedField.source_batch_plain_unmarked` in `lean/OAI/NumberTheory/DirichletL/Detector/DetectorPlainUnmarkedRestrictedField.lean` (OpenAI); the definitions it uses are in the definitions bundles of this split (OpenAI's, carved) and in wurtle's bundle `HeckeSevenEighths`.
-- source:
--   OpenAI, The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re s > 7/8, OpenAI Math Release, September 30, 2026, family 003 of https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory/DirichletL

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_HeckeSevenEighths
import Definitions.Def_OAIHecke78B027

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.ProbeDetectorPlainUnmarkedRestrictedField
open HeckeDyadic HeckeRowClosure HeckeInverseAmplification
open CenteredMomentDetectorPlainFiberSource
open HeckeFamily HeckeDetectorRawFiber HeckeDetectorBatch ProbeHighRowFamily
open HeckeDetectorRowwisePolynomial HeckeDetectorDyadicProfiles
open CenteredMomentDetectorDictionary CenteredMomentDetectorEnergyInitialState
open CenteredMomentDetectorPlainExceptional CenteredMomentDetectorPlainUnmarkedState
open CenteredMomentDetectorPlainMomentParameters
open CenteredMomentEnergyState CenteredMomentEnergyBands CenteredMomentNaturalFixedRaySource
open QuadraticInitialBound
local notation "O" => HeckeFamily.O

open ProbeDetectorPlainUnmarkedField
variable {Δ:ℝ}

theorem source_batch_plain_unmarked (D:Parameters.HighData Δ)
    (S:ProbeFinalAssembly.SourceData D)
    (henergy:∃degree:ℕ,∃control:Finset (ℕ×ℕ),∀η₀:Character,
      ∃A:ℝ,0<A ∧ ∀ᶠU:ℝ in atTop,
        ZeroAt (internalQ (sourceFixedIdeal S) η₀) (1/4) (9/4) radialSupportUpper 0 1 2 (D.t/4) U degree control A):
    ∃Jheight:ℕ,∀η:Character,∃C:ℝ,0<C ∧
    ∀ᶠZ:ℝ in atTop,1<Z ∧ ∀rows:Finset FreeRow,
      (∀u∈rows,Z^(1/100:ℝ)≤ rowNorm u)→
      ∀d:ℝ,(1/200:ℝ)≤d→∀(a tstar T heightAllowance:ℝ)(i:ℕ)
      (B:Batch S.modulus ⊤ (Sum Bool (RayQuotient.Characters S.modulus ⊤)) (Fin D.N)
        (Z^d) a D.ε tstar T heightAllowance i),B.rows⊆rows→
      B.data=sourceMomentData S.modulus ⊤ le_top S.S S.exclusions.prime η→
      B.profile=(fun _ x=>(S.w x:ℂ))→B.widths=(fun s=>D.ell s/d)→
      ∀bin label left right,∀hne:(B.fiberRows bin label left right).Nonempty,
      ∀height:ℝ,0≤height→∀j k:ℕ,j+k≤2→
      ∀σ∈Set.Icc (0:ℝ) 1,∀t∈Set.Icc (-height) height,
      let F:=B.fiber bin label left right hne;
      let value:=∑u∈F.rows,‖polynomial (F.family u F.label) false ((logProfile^[j]) positiveAnnular)
        ((Z^d)^F.m) σ t*polynomial (F.family u F.label) false ((logProfile^[k]) positiveAnnular)
        ((Z^d)^F.m) σ t‖^2;
      value≤C*(1+height)^Jheight*(Z^d)^(max 1 (2*F.m)+D.t) ∧
      value≤C*(1+height)^Jheight*max (Z^d) (((Z^d)^F.m)^2)*(Z^d)^D.t := by
  sorry

end SevenEighths.ProbeDetectorPlainUnmarkedRestrictedField

end

end OAI
end
