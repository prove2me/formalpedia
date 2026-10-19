-- Prove2me | Theorems.Thm_OAI_KervaireSpectral_exists_phaseOperator
-- name    : OAI.KervaireSpectral.exists_phaseOperator
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T17:38:06.825561+00:00
-- url     : https://prove2.me/theorems/c1358afd-ea77-47cb-846b-63e7cd06173c
-- title:
--   The phase operator of a unitary
-- statement:
--   Let $U$ be a unitary on a complex Hilbert space $H$. There is an operator $B$ with $0\le B\le1$ and $\|B\|\le1$ such that
--   $$
--   e^{2\pi iB}=U,\qquad\mathrm{Re}\langle\xi,B\xi\rangle=\int\mathrm{ph}(z)\,d\mu_\xi(z)\ \ \text{for all }\xi .
--   $$
--   Here $\mathrm{ph}(z)$ is the fractional part of $\arg z/2\pi$ and $\mu_\xi$ is the spectral measure of $\xi$. Moreover $B$ commutes with every operator commuting with $U$ and $U^*$.
--
--   So $B=\mathrm{ph}(U)$ is the phase operator of $U$, with spectrum in $[0,1]$, and it lies in every von Neumann algebra containing $U$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/Kervaire/SpectralLogarithm.lean#L19-L100

import Mathlib
import Definitions.Def_Kervaire
import Definitions.Def_OAI_GroupTheory_Kervaire_Reductions
import Definitions.Def_OAI_GroupTheory_Kervaire_PermutationCycles
import Definitions.Def_OAI_GroupTheory_Kervaire_Components
import Definitions.Def_OAI_GroupTheory_Kervaire_Suppression
import Definitions.Def_OAI_GroupTheory_Kervaire_ComponentFibers
import Definitions.Def_OAI_GroupTheory_Kervaire_StrongLimits
import Definitions.Def_OAI_GroupTheory_Kervaire_SpectralMeasures
import Definitions.Def_OAI_GroupTheory_Kervaire_SpectralLogarithm

open OAI OAI.KervaireSpectral
open Filter
open scoped Topology
open scoped CompactlySupported ComplexOrder
open MeasureTheory Filter
open scoped Topology
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
open KervaireStrong

theorem OAI.KervaireSpectral.exists_phaseOperator (U : Operator H) (hU : U ∈ unitary (Operator H)) :
    letI := isStarNormal_of_mem_unitary hU
    ∃ B : Operator H, 0 ≤ B ∧ B ≤ 1 ∧ ‖B‖ ≤ 1 ∧
      NormedSpace.exp ((((2 * Real.pi : ℝ) : ℂ) * Complex.I) • B) = U ∧
      (∀ ξ, (inner ℂ ξ (B ξ)).re = vectorPhase U ξ) ∧
      ∀ R, Commute U R → Commute (star U) R → Commute B R := by sorry
