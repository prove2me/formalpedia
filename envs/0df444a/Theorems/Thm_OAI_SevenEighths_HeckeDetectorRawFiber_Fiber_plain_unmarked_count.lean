-- Prove2me | Theorems.Thm_OAI_SevenEighths_HeckeDetectorRawFiber_Fiber_plain_unmarked_count
-- name    : OAI.SevenEighths.HeckeDetectorRawFiber.Fiber.plain_unmarked_count
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-09T02:22:30.239629+00:00
-- url     : https://prove2.me/theorems/37840225-42ec-4db6-b86c-caa5553f598c
-- title:
--   Row count of a fiber from plain unmarked moments
-- statement:
--   Let $F$ be a `Fiber` with `Moments F Δ c κ C height εm`, $U>1$, $a\ge0$, $C,\mathrm{height}\ge0$ with $2\pi\,\mathrm{allowance}+3iT\le\mathrm{height}$. Then the number of rows of $F$ is at most $192(1+\mathrm{height})C\cdot U^{\max(1,2F.m)-2(2a-1)F.m+4\varepsilon+\varepsilon_m}$.
--
--   Lean: `OAI.SevenEighths.HeckeDetectorRawFiber.Fiber.plain_unmarked_count` in `lean/OAI/NumberTheory/DirichletL/Hecke/DetectorRawBranches.lean` (OpenAI); the definitions it uses are in the definitions bundles of this split (OpenAI's, carved) and in wurtle's bundle `HeckeSevenEighths`.
-- source:
--   OpenAI, The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re s > 7/8, OpenAI Math Release, September 30, 2026, family 003 of https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory/DirichletL

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_HeckeSevenEighths
import Definitions.Def_OAIHecke78B024

section

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.HeckeDetectorRawFiber
open HeckeFamily HeckeDyadic HeckeDetectorWitnessRows HeckeDetectorSupportedWitness
open HeckeDetectorInverseFiberCount
variable {M : Ideal O} {H : Subgroup (O ⧸ M)ˣ} {Label Slot : Type*}
  {U a ε tstar T allowance : ℝ} {i : ℕ}

theorem Fiber.plain_unmarked_count (F : Fiber M H Label Slot U a ε tstar T allowance i)
    {Δ c κ C height εm : ℝ} (moments : Moments F Δ c κ C height εm)
    (hU : 1<U) (ha : 0≤a) (hC : 0≤C) (hh : 0≤height)
    (hf : 2*Real.pi*allowance+(3*i : ℕ)*T≤height) :
    (F.rows.card : ℝ)≤(192*(1+height)*C)*U^(max 1 (2*F.m)-2*(2*a-1)*F.m+4*ε+εm) := by
  sorry

end SevenEighths.HeckeDetectorRawFiber

end

end OAI
end
