-- Prove2me | Theorems.Thm_OAI_SevenEighths_HeckeDetectorRawFiber_Fiber_inverse_marked_count
-- name    : OAI.SevenEighths.HeckeDetectorRawFiber.Fiber.inverse_marked_count
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-09T02:14:32.360978+00:00
-- url     : https://prove2.me/theorems/334ebd28-9e66-4346-bfe2-6a13d2fb8bd3
-- title:
--   Row count of a fiber from inverse marked moments
-- statement:
--   Let $F$ be a `Fiber M H Label Slot U a ε tstar T allowance i` with `Moments F Δ c κ C height εm`, and assume $U>1$, $a\ge1/2$, $C\ge0$, $\mathrm{height}\ge0$ with $2\pi\,\mathrm{allowance}+3iT\le\mathrm{height}$, and $0\le z\le7/37$ with $F.r+2z<1$ and $2F.r+8z<3$. Then the number of rows of $F$ is at most $12(1+\mathrm{height})C\cdot U^{1-(2a-1)F.r-2F.q\,z+2\varepsilon+(2a-1)F.\mathrm{mesh}+\varepsilon_m}$.
--
--   Lean: `OAI.SevenEighths.HeckeDetectorRawFiber.Fiber.inverse_marked_count` in `lean/OAI/NumberTheory/DirichletL/Hecke/DetectorRawBranches.lean` (OpenAI); the definitions it uses are in the definitions bundles of this split (OpenAI's, carved) and in wurtle's bundle `HeckeSevenEighths`.
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

theorem Fiber.inverse_marked_count (F : Fiber M H Label Slot U a ε tstar T allowance i)
    {Δ c κ C height εm : ℝ} (moments : Moments F Δ c κ C height εm)
    (hU : 1<U) (ha : 1/2≤a) (hC : 0≤C) (hh : 0≤height)
    (hf : 2*Real.pi*allowance+(3*i : ℕ)*T≤height)
    (z : ℝ) (hz : 0≤z) (hz' : z≤7/37) (hcap1 : F.r+2*z<1) (hcap2 : 2*F.r+8*z<3) :
    (F.rows.card : ℝ)≤(12*(1+height)*C)*U^(1-(2*a-1)*F.r-2*F.q*z+2*ε+(2*a-1)*F.mesh+εm) := by
  sorry

end SevenEighths.HeckeDetectorRawFiber

end

end OAI
end
