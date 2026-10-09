-- Prove2me | Theorems.Thm_OAI_SevenEighths_ProbeHighRowFamily_actual_source_batch
-- name    : OAI.SevenEighths.ProbeHighRowFamily.actual_source_batch
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-09T02:20:55.246062+00:00
-- url     : https://prove2.me/theorems/d2af6ec7-5690-49d6-9f96-9bb65d78d95e
-- title:
--   Source batches exist with the prescribed data
-- statement:
--   Let $M\ne0$, $H\supseteq$`globalUnits M`, $S$ maximal with `SourceExclusions S`, $\eta$ a `Character`, and reals $0<d_{\min}\le d_{\max}\le37/42$, $0<\tau<d_{\min}/2$ with $4\tau<d_{\min}\,\mathrm{heightCost}$, $\varepsilon>0$, $0<e<1/1000$, $0<\kappa\le1$, $\mathrm{heightCost}\ge0$, `margin` $>0$, `mesh` $\ge0$, `binWidth` $>0$, $I\in\mathbb N$. Then, under the remaining hypotheses of the Lean, for all admissible rows, slot widths $\ell$, profiles $W$, upper bounds and external points $z$ there is a `Batch` $B$ at $U=Z^d$ with rows the given rows, data `sourceMomentData M H hH S _ η`, reverse `sourceMomentReverse M H`, all slots, widths $\ell_j/d$, profile $W$, the given upper and external data, mesh and bin width, and family `sourceDetectorFamily S _ η u (rayCubeFamily M H hH u)` at every row.
--
--   Lean: `OAI.SevenEighths.ProbeHighRowFamily.actual_source_batch` in `lean/OAI/NumberTheory/DirichletL/Detector/SourceBatch.lean` (OpenAI); the definitions it uses are in the definitions bundles of this split (OpenAI's, carved) and in wurtle's bundle `HeckeSevenEighths`.
-- source:
--   OpenAI, The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re s > 7/8, OpenAI Math Release, September 30, 2026, family 003 of https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory/DirichletL

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_HeckeSevenEighths
import Definitions.Def_OAIHecke78B027

section

namespace OAI

noncomputable section
open scoped Classical BigOperators Topology
open Filter
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification HeckeDetectorBatch ProbePhysical
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M]
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

attribute [local instance] OAI.SevenEighths.ProbeHighRowFamily.instFiniteQuotientOIdeal
theorem actual_source_batch (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (hmax : ∀P∈S,P.IsMaximal) (η : Character)
    (dmin dmax τ ε e κ heightCost margin mesh binWidth : ℝ) (I : ℕ)
    (hdmin : 0<dmin) (hdmax : dmin≤dmax) (hdtop : dmax≤37/42) (hτ : 0<τ)
    (hτzero : τ<dmin/2) (hτheight : 4*τ<dmin*heightCost)
    (hε : 0<ε) (he : 0<e) (he' : e<1/1000) (hκ : 0<κ) (hκ' : κ≤1) (hheightCost : 0≤heightCost)
    (hmargin : 0< margin) (hm : 0≤ mesh) (hb : 0<binWidth)
    (hbudget : 12*e*((22:ℝ)+2)+8*κ+2*heightCost≤ε/2) :
    ∀ᶠZ : ℝ in atTop,∀d : ℝ,dmin≤d → d≤dmax →
    ∀(U : ℝ) (rows : Finset FreeRow),rows.Nonempty → rows⊆rowBand (Z^(1/100:ℝ)) U →
      (∀u∈rows,(calibrationForSet S hmax).residueMonoid u.val≠0) →
      (∀u∈rows,rowNorm u≤Z^(d-margin)) →
    ∀(a : ℝ) (i : ℕ),i≤I → 51/100<a → a≤1 →
      (∀u∈rows,detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u)) (3*(i+1:ℕ)*Z^τ)<a+2*e) →
      (∀u∈rows,a≤detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u)) ((3*i:ℕ)*Z^τ)) →
    ∀tstar : ℝ,1≤tstar → tstar≤3/2 →
    ∀(N : ℕ) (ell : Fin N→ℝ),(∀j,0<ell j) → (∀j,ell j≤dmin*mesh) → (∑j,ell j)=1/6 →
    ∀(W : Fin N→ℝ→ℂ) (upper : Fin N→ℝ) (z : Fin N→ℂ),
    ∃B : Batch M H (Sum Bool (RayQuotient.Characters M H)) (Fin N)
        (Z^d) a ε tstar (Z^τ) ((Z^d)^(τ/(2*dmax))) i,
      B.rows=rows ∧ B.data=sourceMomentData M H hH S hS.prime η ∧
      B.reverse=sourceMomentReverse M H ∧ B.slots=Finset.univ ∧
      B.widths=(fun j=>ell j/d) ∧ B.profile=W ∧ B.upper=upper ∧ B.external=z ∧
      B.mesh=mesh ∧ B.binWidth=binWidth ∧
      (∀u∈rows,∀j,B.family u j=sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u) j) := by
  sorry
end SevenEighths.ProbeHighRowFamily

end

end OAI
end
