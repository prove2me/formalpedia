-- Prove2me | Theorems.Thm_OAI_SevenEighths_CenteredMomentSecondCanonicalScalar_actual_retained_scalar_norm
-- name    : OAI.SevenEighths.CenteredMomentSecondCanonicalScalar.actual_retained_scalar_norm
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-09T02:22:09.44077+00:00
-- url     : https://prove2.me/theorems/f720b139-66d7-4a20-b036-66089d2fdc0d
-- title:
--   The retained scalar times the ideal correlation has norm at most 1
-- statement:
--   Let $C,D$ be `Supported` ideals of the Eisenstein integers with the same prime support, $U\subseteq$`CommonIndex C D`, $R\in\mathbb R$ and $h\in\mathcal O$. Then $\|\texttt{retainedScalar}\,C\,D\,U\,R\,h\cdot\texttt{idealCorrelation}\,C\,D\,((\texttt{commonFrequencyGenerator}\,C\,D\cdot\texttt{nonunitFrequencyGenerator}\,C\,D\,U)\,h)\|\le1$.
--
--   Lean: `OAI.SevenEighths.CenteredMomentSecondCanonicalScalar.actual_retained_scalar_norm` in `lean/OAI/NumberTheory/DirichletL/Moments/SecondCanonicalScalar.lean` (OpenAI); the definitions it uses are in the definitions bundles of this split (OpenAI's, carved) and in wurtle's bundle `HeckeSevenEighths`.
-- source:
--   OpenAI, The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re s > 7/8, OpenAI Math Release, September 30, 2026, family 003 of https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory/DirichletL

import Mathlib
import Definitions.Def_HeckeSevenEighths
import Definitions.Def_OAIHecke78B025

section

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentSecondCanonicalScalar
open CanonicalQuadraticSieve CompletedGauss
open CenteredMomentSecondCanonical CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalNonunit
open CenteredMomentCanonicalFirst CenteredMomentPartition CenteredMomentPartitionNorm
open CenteredMomentSectorLocalization CenteredMomentSupport
local notation "O" => ActualEisensteinCubic.O

theorem actual_retained_scalar_norm (C D : Ideal O) (hC : Supported C) (hD : Supported D)
    (hCD : CompletedGauss.primeSupport C=CompletedGauss.primeSupport D)
    (U : Finset (CommonIndex C D)) (R : ℝ) (h : O) :
    ‖retainedScalar C D U R h*idealCorrelation C D hC hD
      ((commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U)*h)‖≤1 := by
  sorry

end SevenEighths.CenteredMomentSecondCanonicalScalar

end

end OAI
end
