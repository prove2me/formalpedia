-- Prove2me | Theorems.Thm_OAI_SevenEighths_InverseMoment_original_marked_binned_energy
-- name    : OAI.SevenEighths.InverseMoment.original_marked_binned_energy
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T23:52:57.023834+00:00
-- url     : https://prove2.me/theorems/6b883935-cf8f-4992-9324-251974dc4829
-- title:
--   Marked canonical row split into short sum and cube bins
-- statement:
--   Let $S$ be a finite set of prime ideals of $\mathcal O$ containing `fixedBadPrimes`, $D\in\mathbb N$, $\Psi$ multiplicative, $m,f,z\in\mathcal O$, $W$ compactly supported with $W(t)\ne0\Rightarrow t\le b$, $X>0$ with $bX\le D$, $H_0$ real, and slot data (`slots`, `lists`, `a`) on `primePool (outsideSquarefreeIdeals S D)`. Then $\|\texttt{outsideCanonicalMarkedRow}\cdots\|^2$ is at most
--   $$2X\Big(\|\texttt{markedShortCompletedSum}\cdots\|^2+|\texttt{cubeLogRange}\,b\,X|\sum_{j\in\texttt{cubeLogRange}\,b\,X}\|\texttt{markedReopenedCubeBin}\ S\,D\,(\texttt{activeCubeLogBin}\,S\,D\,b\,X\,j)\cdots\|^2\Big).$$
--
--   Lean: `OAI.SevenEighths.InverseMoment.original_marked_binned_energy` in `lean/OAI/NumberTheory/DirichletL/Descent/ReopenedBins.lean` (OpenAI); the definitions it uses are in the definitions bundles of this split (OpenAI's, carved) and in wurtle's bundle `HeckeSevenEighths`.
-- source:
--   OpenAI, The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re s > 7/8, OpenAI Math Release, September 30, 2026, family 003 of https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory/DirichletL

import Mathlib
import Definitions.Def_OAIHecke78B009

section

namespace OAI

namespace SevenEighths.InverseMoment
noncomputable section
open scoped BigOperators Classical
open ActualEisensteinCubic CompletedGauss CanonicalRowCompletion
open ConcretePrimeRowBridge CanonicalQuadraticSieve SecondPassArithmetic FirstPassCubeLabels
local notation "O" => ActualEisensteinCubic.O

variable {σ : Type*} [DecidableEq σ]
  (S : Finset (Ideal O)) (D : ℕ)
  (Ψ : O→*ℂ) (m f z : O) (W : ℝ→ℂ) (b X H₀ : ℝ)
  (slots : Finset σ)
  (lists : σ→Finset (primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)))
  (a : σ→primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)→ℂ)

theorem original_marked_binned_energy (hbad : fixedBadPrimes⊆S) (hSp : ∀ P∈S,Prime P)
    (hWc : HasCompactSupport W) (hX : 0<X) (hW : ∀ t,W t≠0→t≤b) (hD : b*X≤D) :
    ‖outsideCanonicalMarkedRow S D hbad Ψ m f z slots lists a W X‖^2 ≤
    2*X*(‖markedShortCompletedSum (rowTwist Ψ (m*excludedGenerator S) f z) W X H₀
      (indexedIdealMark (fun i:primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)=>i.val) slots lists a)‖^2 +
    (cubeLogRange b X).card*∑ j∈cubeLogRange b X,
      ‖markedReopenedCubeBin S D (activeCubeLogBin S D b X j) Ψ m f z W X H₀ slots lists a‖^2) := by
  sorry

end
end SevenEighths.InverseMoment

end OAI
end
