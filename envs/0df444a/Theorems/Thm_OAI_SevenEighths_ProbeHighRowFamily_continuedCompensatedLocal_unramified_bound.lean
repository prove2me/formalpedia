-- Prove2me | Theorems.Thm_OAI_SevenEighths_ProbeHighRowFamily_continuedCompensatedLocal_unramified_bound
-- name    : OAI.SevenEighths.ProbeHighRowFamily.continuedCompensatedLocal_unramified_bound
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-09T02:16:41.213447+00:00
-- url     : https://prove2.me/theorems/bb8b015d-0a63-42c8-b776-9e8e369628dd
-- title:
--   Bound for the unramified compensated local factor
-- statement:
--   Let $\eta$ be a `Character`, $u$ a `FreeRow`, $P$ a `Supported` prime ideal not dividing $(u)$ with $N(P)\ge4$, and $x,w,z$ with $\operatorname{Re}x\ge7/8$, $\operatorname{Re}w\ge1/2$, $\operatorname{Re}z\ge17/50$. Then $\|\texttt{continuedCompensatedLocal}\,\eta\,u\,P\,x\,w\,z\,(\overline{\texttt{idealCoeff}\,\eta\,P}\,N(P)^x)\,(N(P)^{-w})\|\le961$.
--
--   Lean: `OAI.SevenEighths.ProbeHighRowFamily.continuedCompensatedLocal_unramified_bound` in `lean/OAI/NumberTheory/DirichletL/PrimeRows/SelectedBounds.lean` (OpenAI); the definitions it uses are in the definitions bundles of this split (OpenAI's, carved) and in wurtle's bundle `HeckeSevenEighths`.
-- source:
--   OpenAI, The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re s > 7/8, OpenAI Math Release, September 30, 2026, family 003 of https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory/DirichletL

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_HeckeSevenEighths
import Definitions.Def_OAIHecke78B023

section

namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeEuler ProbeRow
open CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss ConcretePrimeRowBridge
local notation "O" => HeckeFamily.O

lemma continuedCompensatedLocal_unramified_bound (η : Character) (u : FreeRow) (P : PrimeIdeal)
    (hs : Supported P.val) (hP : ¬P.val∣Ideal.span {u.val}) (hQ : (4:ℝ)≤P.val.absNorm)
    (x w z : ℂ) (hx : (7/8:ℝ)≤x.re) (hw : (1/2:ℝ)≤w.re) (hz : (17/50:ℝ)≤z.re) :
    ‖continuedCompensatedLocal η u P hs x w z
      (star (idealCoeff η P.val)*(P.val.absNorm:ℂ)^x) ((P.val.absNorm:ℂ)^(-w))‖≤961 := by
  sorry

end SevenEighths.ProbeHighRowFamily
end

end OAI
end
