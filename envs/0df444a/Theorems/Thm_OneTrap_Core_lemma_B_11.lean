-- Prove2me | Theorems.Thm_OneTrap_Core_lemma_B_11
-- name    : OneTrap.Core.lemma_B_11
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T02:46:58.545506+00:00
-- url     : https://prove2.me/theorems/5264daa2-9ee0-4724-b81e-144c014cd511
-- title:
--   Lemma B.11 — a small cost increase lowers a positive finite index continuously, and $c\mapsto V_P(w\mid A(c))$ is upper semicontinuous on the nonnegative orthant
-- statement:
--   Fix $w\in W_{\mathrm{eff}}$. (i) Increasing by $\delta>0$ the cost of a finite-index unknown box whose index exceeds zero moves its index strictly downward for all sufficiently small $\delta$, and the index converges to its original value as $\delta\downarrow 0$. (ii) For a fixed finite collection of output laws, let $A(c)$ be the technology with cost vector $c$; then $c\mapsto V_P(w\mid A(c))$ is upper semicontinuous on the nonnegative cost orthant.
--
--   Differences from the source:
--   - encoding: ρ_i: the smallest extended-real solution of c_i = E[(X_i − ρ_i)+], with (X − ∞)+ := 0 → `resv w b` = `sInf` in EReal of the r with ∫⁻ ((w y : EReal) − r).toENNReal dF = ofReal c; reason: in EReal, X − ⊤ = ⊥ whose positive part is 0, and X − ⊥ = ⊤; the solution set is closed, so its infimum is its least element when it is nonempty (Lemma B.12)
--   - encoding: V_P(w | A) = max of P_A(w, π) over Σ⋆(w, A) = argmax U_A(w, ·) (Definition 2.2) → `VP w T` = `sSup` in EReal of `principalValue` over `agentOptimal` (⊥ if that set were empty); the null output is the initial outcome with pair (w 0, 0 − w 0); reason: both maxima are attained (Fact A.1), and an attained supremum is the maximum
--   - encoding: a finite-index unknown box whose index exceeds zero → any output law G and cost c ≥ 0 with 0 < resvOf w G c < ⊤; reason: the index depends only on the law, the cost and w, and every such pair can be an unknown box
--   - encoding: for all sufficiently small δ; converges as δ ↓ 0 → ∃ δ₀ > 0 with the strict inequality for 0 < δ < δ₀; `Tendsto` along `nhdsWithin 0 (Ioi 0)` in EReal; reason: the same notions
--   - encoding: A(c), c in the nonnegative cost orthant → `fun i => Box.ofCost (F i) (c i)` (cost max (c i) 0) and `UpperSemicontinuousOn` on {c | ∀ i, 0 ≤ c i}; reason: on the orthant the clamp is the identity, and `UpperSemicontinuousOn` sees only points of the orthant
-- source:
--   Feldman, Fu, Peng, Tang (2026), One Trap Is Enough: The Structure and Complexity of Robust Contracts for Sequential Search, held STOC 2027 submission (SHA-256 8b684ffb…cf066), Lemma B.11, p. 31 (PDF 32)

import Mathlib
import Definitions.Def_OneTrap_Core_Model
import Definitions.Def_OneTrap_Core_Search
import Definitions.Def_OneTrap_Core_Index

open MeasureTheory

namespace OneTrap.Core

/-- Lemma B.11 (p. 31). (i) Raising by `δ > 0` the cost of a box whose index is finite and
positive moves its index strictly down for all small `δ`, and the index converges to the
original one as `δ ↓ 0`. (ii) For fixed output laws, the map `c ↦ V_P(w | A(c))` is upper
semicontinuous on the nonnegative cost orthant. -/
theorem lemma_B_11 {ι : Type*} [Fintype ι] [DecidableEq ι] (w : ℝ → ℝ) (hw : IsEffContract w)
    (F : ι → OutputLaw) :
    (∀ (G : OutputLaw) (c : ℝ), 0 ≤ c → 0 < resvOf w G c → resvOf w G c < ⊤ →
      (∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ → resvOf w G (c + δ) < resvOf w G c) ∧
      Filter.Tendsto (fun δ : ℝ => resvOf w G (c + δ)) (nhdsWithin 0 (Set.Ioi 0))
        (nhds (resvOf w G c))) ∧
    UpperSemicontinuousOn (fun c : ι → ℝ => VP w fun i => Box.ofCost (F i) (c i))
      {c : ι → ℝ | ∀ i, 0 ≤ c i} := by sorry

end OneTrap.Core
