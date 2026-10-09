-- Prove2me | Theorems.Thm_OAI_SevenEighths_ProbeDetectorInverseMarkedField_source_batch_inverse_marked
-- name    : OAI.SevenEighths.ProbeDetectorInverseMarkedField.source_batch_inverse_marked
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-09T02:20:17.028064+00:00
-- url     : https://prove2.me/theorems/460f1c27-e57e-4928-9326-a3c8eaeaa133
-- title:
--   Inverse marked fiber energies of source batches
-- statement:
--   Let $M\ne0$, $H\supseteq$`globalUnits M`, and $S$ `SourceData` over `HighData` $D$. Then there is $J$ such that for every `Character` $\eta$ there is $C>0$ with: eventually in $Z$ ($Z>1$), for every $d\ge1/200$, every source `Batch` $B$ at $U=Z^d$ with the data of the Lean, every nonempty fiber $F$ and selected slots with $F.r+2\sum w<1$ and $2F.r+8\sum w<3$, $n\le2$, $s\in[0,1]$, $t\in[-\mathrm{height},\mathrm{height}]$:
--   $$\sum_{u\in F.\mathrm{rows}}\|\texttt{polynomial}(\dots)\,\mathrm{true}\,(\texttt{logProfile}^{[n]}\,F.\texttt{inverseProfile})\,(Z^d)^{F.r}\,s\,t\cdot F.\texttt{physicalProduct}\,\mathrm{selected}\,u\|^2\le C(1+\mathrm{height})^J(Z^d)^{1+D.t}.$$
--
--   Lean: `OAI.SevenEighths.ProbeDetectorInverseMarkedField.source_batch_inverse_marked` in `lean/OAI/NumberTheory/DirichletL/Detector/DetectorInverseMarkedField.lean` (OpenAI); the definitions it uses are in the definitions bundles of this split (OpenAI's, carved) and in wurtle's bundle `HeckeSevenEighths`.
-- source:
--   OpenAI, The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re s > 7/8, OpenAI Math Release, September 30, 2026, family 003 of https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory/DirichletL

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_HeckeSevenEighths
import Definitions.Def_OAIHecke78B027

section

namespace OAI

noncomputable section

open scoped Classical BigOperators Topology SchwartzMap ContDiff
namespace SevenEighths.ProbeDetectorInverseMarkedField
open HeckeFamily HeckeDyadic HeckeInverseAmplification InverseMoment
open HeckeDetectorRawFiber HeckeDetectorBatch HeckeDetectorCoefficientTransfer
open ProbeHighRowFamily ProbeFinalAssembly Filter
open DetectorDictionaryInverseMarkedReference DetectorDictionaryInverseClippedUniform
local notation "O"=>HeckeFamily.O

variable (M:Ideal O)[NeZero M]
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)

attribute [local instance] OAI.SevenEighths.ProbeDetectorInverseMarkedField.instFiniteQuotientOIdeal
attribute [local instance] OAI.SevenEighths.ProbeDetectorInverseMarkedField.instFintypeSumBoolSubtypeMulCharQuotientOIdealComplexMemSubgroupCharacters
theorem source_batch_inverse_marked {Δ:ℝ}{D:Parameters.HighData Δ}
    (S:SourceData D):
    ∃J:ℕ,∀η:Character,∃C:ℝ,0<C ∧ ∀ᶠZ:ℝ in atTop,
    1<Z ∧ ∀d:ℝ,(1/200:ℝ)≤d →
    ∀(a ε tstar T allowance:ℝ)(i:ℕ)
      (B:Batch M H (Sum Bool (RayQuotient.Characters M H)) (Fin D.N)
        (Z^d) a ε tstar T allowance i),
      B.data=sourceMomentData M H hH S.S S.exclusions.prime η →
      B.profile=(fun _ x=>(S.w x:ℂ)) → B.upper=(fun _=>2) →
      B.widths=(fun s=>D.ell s/d) → (∀s,(B.external s).re=17/50) →
    ∀bin label left right,∀hne:(B.fiberRows bin label left right).Nonempty,
    ∀height:ℝ,0≤height →
    let F:=B.fiber bin label left right hne;
    ∀selected:Finset (Fin D.N),selected⊆F.slots →
      F.r+2*(∑s∈selected,F.widths s)<1 → 2*F.r+8*(∑s∈selected,F.widths s)<3 →
    ∀n:ℕ,n≤2 → ∀s∈Set.Icc (0:ℝ) 1,∀t∈Set.Icc (-height) height,
      (∑u∈F.rows,‖polynomial (F.family u F.label) true
        ((HeckeDetectorRowwisePolynomial.logProfile^[n]) F.inverseProfile)
        ((Z^d)^F.r) s t*F.physicalProduct selected u‖^2)≤
        (C*(1+height)^J)*(Z^d)^(1+D.t) := by
  sorry

end SevenEighths.ProbeDetectorInverseMarkedField

end

end OAI
end
