-- Prove2me | Theorems.Thm_OAI_ThresholdParallelRepetition_MeasurementTransport_transportedEffect_pullback
-- name    : OAI.ThresholdParallelRepetition.MeasurementTransport.transportedEffect_pullback
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T10:43:35.605257+00:00
-- url     : https://prove2.me/theorems/266026d3-42e1-481d-8417-e46cefe97c61
-- title:
--   Transported measurement effects pull back to the original effects
-- statement:
--   Let $m,n$ be finite index sets, $\mathcal A$ a finite set of outcomes, and $F\in\mathbb C^{m\times n}$. Put $T=F^*F$, let $T^{+}$ be its support inverse (the functional calculus of $t\mapsto t^{-1}$ with $0^{-1}=0$, i.e. the Moore–Penrose pseudoinverse of $T$), and let $\Pi_F=F\,T^{+}F^*$, the orthogonal projection onto the column space of $F$. Given $n\times n$ matrices $G_a$ ($a\in\mathcal A$) and a distinguished outcome $a_0\in\mathcal A$, the transported effects are the $m\times m$ matrices
--   $$
--   E_a=\big(FT^{+}\big)\,G_a\,\big(FT^{+}\big)^*+\mathbf 1[a=a_0]\,\big(I_m-\Pi_F\big),\qquad a\in\mathcal A .
--   $$
--
--   **Theorem.** If every $G_a$ is positive semidefinite and $\sum_{a\in\mathcal A}G_a=F^*F$, then for all $a_0,a\in\mathcal A$
--   $$
--   F^*\,E_a\,F=G_a .
--   $$
--
--   Under the same hypotheses the matrices $E_a$ are positive semidefinite and sum to $I_m$ (this is proved together with the definition), so $\{E_a\}$ is a genuine measurement on $\mathbb C^m$, completed on the orthogonal complement of the range of $F$ by the outcome $a_0$. The theorem says that this measurement, pulled back through $F$, reproduces the given operators: $\langle Fv,E_aFv\rangle=\langle v,G_av\rangle$ for every $v\in\mathbb C^n$. This is how a family of effects that sums only to $F^*F$ is turned into a measurement on the larger space when measurements of strategies are refined.
--
--   **Formalization Note** `transportedEffect F G a₀ a` is the displayed matrix, with `supportInverse (Fᴴ * F)` for $T^{+}$ and `rangeProjection F` for $\Pi_F$; the corresponding measurement is `POVM.transport`. All index types are finite with decidable equality.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/EntangledGames/MeasurementTransport.lean#L168-L186

import Mathlib
import Definitions.Def_EntangledGames
import Definitions.Def_OAI_Probability_EntangledGames_Basic
import Definitions.Def_OAI_Probability_EntangledGames_Resolvent
import Definitions.Def_OAI_Probability_EntangledGames_SpectralEntropy
import Definitions.Def_OAI_Probability_EntangledGames_Purification
import Definitions.Def_OAI_Probability_EntangledGames_MeasurementTransport

open OAI OAI.ThresholdParallelRepetition OAI.ThresholdParallelRepetition.MeasurementTransport
universe u_n u_m u_A
open scoped BigOperators ComplexOrder
open scoped MatrixOrder
open Matrix
open MeasureTheory Filter Set
open scoped Topology
open scoped Matrix.Norms.Elementwise
open scoped BigOperators MatrixOrder ComplexOrder
open Matrix
variable {n : Type u_n} [Fintype n] [DecidableEq n]
variable {m : Type u_m} [Fintype m] [DecidableEq m]
variable {A : Type u_A} [Fintype A] [DecidableEq A]

theorem OAI.ThresholdParallelRepetition.MeasurementTransport.transportedEffect_pullback (F : Matrix m n ℂ) (G : A → Matrix n n ℂ)
    (hG : ∀ a, (G a).PosSemidef) (hGT : ∑ a, G a = Fᴴ * F) (a₀ a : A) :
    Fᴴ * transportedEffect F G a₀ a * F = G a := by sorry
