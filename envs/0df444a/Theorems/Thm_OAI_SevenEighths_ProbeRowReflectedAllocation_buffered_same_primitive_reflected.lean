-- Prove2me | Theorems.Thm_OAI_SevenEighths_ProbeRowReflectedAllocation_buffered_same_primitive_reflected
-- name    : OAI.SevenEighths.ProbeRowReflectedAllocation.buffered_same_primitive_reflected
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-09T01:50:00.371093+00:00
-- url     : https://prove2.me/theorems/88738a02-ff53-4c7c-9d91-4f7281b51f0e
-- title:
--   Reflected-line bound through a primitive character with the same coefficients
-- statement:
--   For $0<e<1/1000$ and $\varepsilon>0$ there is $C>0$ such that for every finite family of characters $\chi_j$, reals $B>2$, $a\in[51/100,1]$, $i\in\mathbb N$ with `detectorMaximum χ (3(i+1)B)` $<a+2e$, every $j$ with nontrivial residue character and every `Character` $\psi$ whose residue character is primitive on ideals and whose `idealCoeff` agrees with that of $\chi_j$ on ideals coprime to $\chi_j.\mathrm{modulus}$ (and $\chi_j$'s vanishes elsewhere), and every $w$ with $\operatorname{Re}w=1-a-6e$, $|\operatorname{Im}w|\le(3i+2)B$:
--   $$|L(\chi_j,w)|\le C\,N(\psi.\mathrm{modulus})^{a-1/2+6e}N(\texttt{radical}\,\chi_j.\mathrm{modulus})^{6e+2\varepsilon}(3+(3i+2)B)^2(\texttt{presentationComplexity}\,\chi_j\,((3i+2)B))^{\varepsilon}.$$
--
--   Lean: `OAI.SevenEighths.ProbeRowReflectedAllocation.buffered_same_primitive_reflected` in `lean/OAI/NumberTheory/DirichletL/Detector/RowReflectedAllocation.lean` (OpenAI); the definitions it uses are in the definitions bundles of this split (OpenAI's, carved) and in wurtle's bundle `HeckeSevenEighths`.
-- source:
--   OpenAI, The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re s > 7/8, OpenAI Math Release, September 30, 2026, family 003 of https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory/DirichletL

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_HeckeSevenEighths
import Definitions.Def_OAIHecke78B017

section

namespace OAI

noncomputable section
open scoped Classical BigOperators Topology ComplexConjugate
open Set Complex
namespace SevenEighths.ProbeRowReflectedAllocation
open HeckeFamily HeckeInverseAmplification ProbeHighRowFamily
open HeckeFiniteDeletion HeckeReciprocalGrowth HeckeDeletionBounds
local notation "O" => HeckeFamily.O

theorem buffered_same_primitive_reflected (e ε : ℝ)
    (he : 0 < e) (he' : e < 1/1000) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ {ι : Type*} [Fintype ι] (χ : ι → Character)
      (B a : ℝ) (i : ℕ), 2 < B → 51/100 ≤ a → a ≤ 1 →
      detectorMaximum χ (3*(i+1 : ℕ)*B) < a+2*e →
      ∀ (j : ι) (ψ : Character), FiniteFourier.IsPrimitiveOnIdeals ψ.residue →
      (χ j).residue ≠ 1 →
      (∀ I : Ideal O, idealCoeff (χ j) I =
        if IsCoprime I (χ j).modulus then idealCoeff ψ I else 0) →
      ∀ w : ℂ, w.re = 1-a-6*e → |w.im| ≤ (3*i+2 : ℕ)*B →
      ‖LFunction (χ j) w‖ ≤ C * (ψ.modulus.absNorm : ℝ) ^ (a-1/2+6*e) *
        ((radical (χ j).modulus).absNorm : ℝ) ^ (6*e+2*ε) *
        (3+(3*i+2 : ℕ)*B)^2 *
        (presentationComplexity (χ j) ((3*i+2 : ℕ)*B)) ^ ε := by
  sorry

end SevenEighths.ProbeRowReflectedAllocation

end

end OAI
end
