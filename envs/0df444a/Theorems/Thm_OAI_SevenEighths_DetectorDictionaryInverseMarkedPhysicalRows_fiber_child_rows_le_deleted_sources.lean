-- Prove2me | Theorems.Thm_OAI_SevenEighths_DetectorDictionaryInverseMarkedPhysicalRows_fiber_child_rows_le_deleted_sources
-- name    : OAI.SevenEighths.DetectorDictionaryInverseMarkedPhysicalRows.fiber_child_rows_le_deleted_sources
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-09T02:16:40.634305+00:00
-- url     : https://prove2.me/theorems/78b45665-7d4d-42d6-8423-b8698827e050
-- title:
--   Fiber child rows bounded by deleted selected sources
-- statement:
--   Let $F$ be a `Fiber`, `selected` a finite set of slots, $W$ vanishing beyond $b_W$, $v$, lower bounds `lower`, $U>1$, the selected profiles vanishing outside $[\mathrm{lower}_s,F.\mathrm{upper}_s]$, and $N(\texttt{deletedBase}\,F.\mathrm{rowData}.\mathrm{modulus})<\mathrm{lower}_s\,U^{F.\mathrm{widths}_s}$ for selected $s$. Then
--   $$\sum_{u\in F.\mathrm{rows}}\|\texttt{polynomial}(\dots)\,\mathrm{true}\,(\texttt{childLogTest}\,W\,v)\,U^{F.r}\,0\,0\cdot F.\texttt{physicalProduct}\,\mathrm{selected}\,u\|^2\le|\mathrm{Div}|\sum_{j\in\mathrm{Div}}\sum_{u}\|\texttt{deletedSelectedSource}(\dots,\texttt{shiftedExponent}\,F.\mathrm{rowData}\,U\,F.r\,j,\dots,u)\|^2,$$
--   $\mathrm{Div}$ the ideal divisors of the product of the excluded primes of the row data.
--
--   Lean: `OAI.SevenEighths.DetectorDictionaryInverseMarkedPhysicalRows.fiber_child_rows_le_deleted_sources` in `lean/OAI/NumberTheory/DirichletL/Dictionary/InverseMarkedPhysicalRows.lean` (OpenAI); the definitions it uses are in the definitions bundles of this split (OpenAI's, carved) and in wurtle's bundle `HeckeSevenEighths`.
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

namespace SevenEighths.DetectorDictionaryInverseMarkedPhysicalRows
open HeckeFamily HeckeDyadic HeckeInverseAmplification HeckeDetectorRawFiber
open HeckeDetectorCoefficientTransfer HeckeDetectorPhysicalSelection
open InverseInitialPhysicalSlots InverseInitialRawDictionary InverseInitialDetectorSource
open DetectorDictionaryInverseMarkedReference DetectorDictionaryInverseRawInitialGates
open InverseInitialExcludedPeriod CanonicalRowCompletion IdealMobiusDivisorSum InverseMoment
local notation "O"=>HeckeFamily.O

variable {M:Ideal O}[NeZero M]{H:Subgroup (O⧸M)ˣ}{Label Slot:Type*}
  {U a ε tstar T allowance:ℝ}{i:ℕ}

 theorem fiber_child_rows_le_deleted_sources
    (F:Fiber M H Label Slot U a ε tstar T allowance i)(selected:Finset Slot)
    (W:ℝ→ℂ)(v bW:ℝ)(lower:Slot→ℝ)(hU:1<U)
    (hW:∀x,W x≠0→x≤bW)
    (hV:∀s∈selected,∀x,F.profile s x≠0→x∈Set.Icc (lower s) (F.upper s))
    (hlarge:∀s∈selected,((deletedBase F.rowData).modulus.absNorm:ℝ)<lower s*U^(F.widths s)):
    (∑u∈F.rows,‖polynomial (F.family u F.label) true (childLogTest W v) (U^F.r) 0 0*
      F.physicalProduct selected u‖^2)≤
      ((idealDivisors (∏P∈excluded F.rowData,P)).card:ℝ)*
        ∑j∈idealDivisors (∏P∈excluded F.rowData,P),∑u∈F.rows,
          ‖deletedSelectedSource F.rowData M H
            (childLogTest (orientedProfile F.reverse W) (orientedFrequency F.reverse v))
            (fun s:selected=>F.profile s) U (shiftedExponent F.rowData U F.r j)
            0 0 bW (fun s:selected=>F.upper s) (fun s:selected=>F.widths s)
            (fun s:selected=>F.external s) u.val‖^2:= by
  sorry

end SevenEighths.DetectorDictionaryInverseMarkedPhysicalRows

end

end OAI
end
