-- Prove2me | Theorems.Thm_OAI_SevenEighths_ProbeDetectorPlainMarkedFineField_source_batch_plain_marked_fine
-- name    : OAI.SevenEighths.ProbeDetectorPlainMarkedFineField.source_batch_plain_marked_fine
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-09T02:24:13.708995+00:00
-- url     : https://prove2.me/theorems/237a8975-416f-465d-b781-68266462a7c2
-- title:
--   Plain marked fiber energies of source batches with fine slots
-- statement:
--   Let $S$ be `SourceData` over `HighData` $D$, `mesh` $>0$ with $D.\ell_j\le\mathrm{mesh}/200$ and `PositiveFineSourceInput S mesh`. Then there is $J$ such that for every `Character` $\eta$ there is $C>0$ with: eventually in $Z$, for rows of `rowNorm` $\ge Z^{1/100}$, $d\ge1/200$, every source `Batch` with the data of the Lean (profile $S.w$, widths $D.\ell_s/d$, upper $2$, external real part $17/50$), every nonempty fiber $F$, height bounding the external imaginary parts, selected slots with $2F.m+6(3/4+2\Delta)\sum w\le1$, $j+k\le2$, $\sigma\in[0,1]$, $t\in[-\mathrm{height},\mathrm{height}]$: the sum over rows of the squared norms of the products of the two plain polynomials (profiles $\texttt{logProfile}^{[j]},\texttt{logProfile}^{[k]}$ of `positiveAnnular` at $(Z^d)^{F.m}$) and the physical product is at most $C(1+\mathrm{height})^J(Z^d)^{1+D.t}$.
--
--   Lean: `OAI.SevenEighths.ProbeDetectorPlainMarkedFineField.source_batch_plain_marked_fine` in `lean/OAI/NumberTheory/DirichletL/Detector/DetectorPlainMarkedFineField.lean` (OpenAI); the definitions it uses are in the definitions bundles of this split (OpenAI's, carved) and in wurtle's bundle `HeckeSevenEighths`.
-- source:
--   OpenAI, The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re s > 7/8, OpenAI Math Release, September 30, 2026, family 003 of https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory/DirichletL

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_HeckeSevenEighths
import Definitions.Def_OAIHecke78B028

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ComplexConjugate
open Filter

namespace SevenEighths.ProbeDetectorPlainMarkedFineField
open HeckeFamily HeckeDyadic HeckeInverseAmplification HeckeDetectorRawFiber HeckeDetectorBatch
open HeckeDetectorRowwisePolynomial HeckeDetectorDyadicProfiles ProbeHighRowFamily ProbeFinalAssembly
open QuadraticInitialBound CenteredMomentDetectorDictionary
open CenteredMomentEnergyBands CenteredMomentEnergyState CenteredMomentInductionEnergy
open CenteredMomentDetectorEnergyInitialState
open CenteredMomentDetectorPlainMomentParameters CenteredMomentNaturalFixedRaySource
open CenteredMomentFiniteProfileExceptional CenteredMomentDetectorPlainFiberSource
local notation "O"=>HeckeFamily.O

theorem source_batch_plain_marked_fine {Δ:ℝ}{D:Parameters.HighData Δ}
    (S:SourceData D)(mesh:ℝ)(hmesh:0< mesh)(hfine:∀j,D.ell j≤ mesh/200)
    (henergy:PositiveFineSourceInput S mesh):
    ∃J:ℕ,∀η:Character,∃C:ℝ,0<C ∧ ∀ᶠZ:ℝ in atTop,
    1<Z ∧ ∀rows:Finset FreeRow,(∀u∈rows,Z^(1/100:ℝ)≤ rowNorm u)→
    ∀d:ℝ,(1/200:ℝ)≤d→∀(a tstar T allowance:ℝ)(i:ℕ)
    (B:Batch S.modulus ⊤ (Sum Bool (RayQuotient.Characters S.modulus ⊤)) (Fin D.N)
      (Z^d) a D.ε tstar T allowance i),B.rows⊆rows→
    B.data=sourceMomentData S.modulus ⊤ le_top S.S S.exclusions.prime η→
    B.profile=(fun _ x=>(S.w x:ℂ))→B.widths=(fun s=>D.ell s/d)→
    (∀s,B.upper s=2)→(∀s,(B.external s).re=17/50)→
    ∀bin label left right,∀hne:(B.fiberRows bin label left right).Nonempty,
    ∀height:ℝ,0≤height→(∀s,|(B.external s).im|≤height)→
    let F:=B.fiber bin label left right hne;
    ∀selected:Finset (Fin D.N),selected⊆F.slots→
      2*F.m+6*(3/4+2*Δ)*(∑s∈selected,F.widths s)≤1→
    ∀j k:ℕ,j+k≤2→∀σ∈Set.Icc (0:ℝ) 1,∀t∈Set.Icc (-height) height,
      (∑u∈F.rows,‖polynomial (F.family u F.label) false ((logProfile^[j]) positiveAnnular)
        ((Z^d)^F.m) σ t*polynomial (F.family u F.label) false ((logProfile^[k]) positiveAnnular)
        ((Z^d)^F.m) σ t*F.physicalProduct selected u‖^2)≤
        (C*(1+height)^J)*(Z^d)^(1+D.t):= by
  sorry
end SevenEighths.ProbeDetectorPlainMarkedFineField

end

end OAI
end
