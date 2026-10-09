-- Prove2me | Theorems.Thm_OAI_SevenEighths_CenteredMomentCommonPairedSource_whole_paired_columns
-- name    : OAI.SevenEighths.CenteredMomentCommonPairedSource.whole_paired_columns
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-09T02:23:13.982861+00:00
-- url     : https://prove2.me/theorems/fcc7aeae-6f75-4ffb-a8da-192a226ee28c
-- title:
--   Paired normalized columns split over allocations
-- statement:
--   For `Input`s $s,v$, `Supported` ideals $C,D$, ideals $R$, `seed` dividing $C$ and $D$, a finite set $D_s$ of ideals and finite `rows`:
--   $$\sum_{L\in D_s}|\mu(L)|\sum_{z}\|\texttt{normalizedColumn}\,s\,C\dots L\,z\|\,\|\texttt{normalizedColumn}\,v\,D\dots L\,z\|\le\sum_{B}\sum_{E}\|\texttt{commonScalar}\,s\,C\,R\,B\|\,\|\texttt{commonScalar}\,v\,D\,R\,E\|\sum_L|\mu(L)|\sum_z\|\texttt{maskedAmplitude}(\texttt{commonData}\,s\,C\,R\,B)\,L\,z\|\,\|\texttt{maskedAmplitude}(\texttt{commonData}\,v\,D\,R\,E)\,L\,z\|,$$
--   $B,E$ over the actual allocations of $C$, $D$.
--
--   Lean: `OAI.SevenEighths.CenteredMomentCommonPairedSource.whole_paired_columns` in `lean/OAI/NumberTheory/DirichletL/Moments/CommonPairedSource.lean` (OpenAI); the definitions it uses are in the definitions bundles of this split (OpenAI's, carved) and in wurtle's bundle `HeckeSevenEighths`.
-- source:
--   OpenAI, The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re s > 7/8, OpenAI Math Release, September 30, 2026, family 003 of https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory/DirichletL

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_HeckeSevenEighths
import Definitions.Def_OAIHecke78B028

section

namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentCommonPairedSource
open HeckeFamily UniqueFactorizationMonoid CanonicalQuadraticSieve
open CenteredMomentCommonLinearSource CenteredMomentCommonLinearNormalization
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentExceptionalMaskedSource CenteredMomentExceptionalAmplitudePair
local notation "O" => HeckeFamily.O
variable {ι κ:Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

theorem whole_paired_columns (s:Input ι)(v:Input κ)(C D:Ideal O)(hC:Supported C)(hD:Supported D)
    (R seed:Ideal O)(hsC:seed∣C)(hsD:seed∣D)(Ds:Finset (Ideal O))(rows:Finset O):
    (∑L∈Ds,‖(moebius L:ℂ)‖*∑z∈rows,
      ‖normalizedColumn s C hC R seed L z‖*‖normalizedColumn v D hD R seed L z‖)≤
      ∑B:actualAllocations s.pools C,∑E:actualAllocations v.pools D,
        (‖commonScalar s C R B‖*‖commonScalar v D R E‖)*
          ∑L∈Ds,‖(moebius L:ℂ)‖*∑z∈rows,
            ‖maskedAmplitude (commonData s C R B) L z‖*
              ‖maskedAmplitude (commonData v D R E) L z‖:= by
  sorry

end SevenEighths.CenteredMomentCommonPairedSource

end

end OAI
end
