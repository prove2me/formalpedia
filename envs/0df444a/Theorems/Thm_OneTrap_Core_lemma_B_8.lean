-- Prove2me | Theorems.Thm_OneTrap_Core_lemma_B_8
-- name    : OneTrap.Core.lemma_B_8
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T02:46:41.952562+00:00
-- url     : https://prove2.me/theorems/f9464168-973a-41a1-acdd-03d3b3d2691d
-- title:
--   Lemma B.8 — local substitution of a deterministic trap at a known index level: $P_I\ge P_{II}-\Delta$
-- statement:
--   Fix $w\in W_{\mathrm{eff}}$. Let $\lambda>0$ be a positive finite known index level and $B$ a block of index-$\lambda$ boxes, all other remaining boxes having lower index. Problem I has incumbent $(\lambda,h^{\mathrm I})$ and remaining index-$\lambda$ boxes $B$; Problem II has incumbent $(x,h^{\mathrm{II}})$ with $x\le\lambda$ and index-$\lambda$ boxes $B$ plus a deterministic trap paying wage $x_T\ge\lambda$, leaving residual $h_T$ and costing $x_T-\lambda$; both have the same lower-index boxes. If $P_I,P_{II}$ are the principal-favored continuation values, then
--   $$P_I\ge P_{II}-\Delta,\qquad \Delta=\begin{cases}\max\{0,h_T-h^{\mathrm I}\},&x<\lambda,\\ \max\{0,h_T-h^{\mathrm I},h^{\mathrm{II}}-h^{\mathrm I}\},&x=\lambda.\end{cases}$$
--
--   Differences from the source:
--   - encoding: U(R, x, h) and P(R, x, h): the agent's optimal value from the state and the best principal value among the policies attaining it → `Ubell`/`Pbell`: the optimal values of the search problem whose openable boxes are R and whose only initially available outcome is (x, h) (agent value as a supremum over policies, principal value as `pfValue`); reason: stopping yields exactly (x, h), as u_stop = x and p_stop = h in (17); earlier outcomes are lexicographically below the incumbent and the remaining outputs are independent of the past
--   - encoding: a deterministic trap paying wage x_T ≥ λ, leaving residual h_T, costing x_T − λ → `trap w y λ hy hxT`: output y ≥ 0 with x_T = w(y) ≥ λ, h_T = y − w(y), cost w(y) − λ, as the extra box `Sum.inr ()` of `ι ⊕ Unit`; reason: a deterministic box is a Dirac output law; its wage and residual are those of its output
--   - encoding: Problems I and II with the same lower-index boxes → a remaining set R ⊇ B whose boxes outside B have index < λ; Problem I is `Pbell w T R λ hI`, Problem II is `Pbell` on `Sum.elim T trap` with openable set `R.disjSum {()}` and incumbent (x, hII); reason: the same boxes in both problems, plus the trap in Problem II
--   - encoding: P_I ≥ P_II − Δ → `Pbell … II − (Δ : EReal) ≤ Pbell … I`; reason: the values are finite (Lemma B.1); Δ is real
--   - reading: λ: the index of a block of known boxes, a known index level of §B.1.3 (λ_1 > … > λ_{ℓ_K} > 0, positive and finite); the proof applies Lemma B.6, which assumes λ > 0 → hypothesis `hlam : 0 < lam` (λ real, so finite); reason: the standing meaning of λ in §B.1.3, where Lemma B.8 is applied only at a level t > 0 equal to a known reservation value
--   - generalization: the incumbent wage x of a state: the highest observed wage, so x ≥ 0 (the null output pays w(0) = 0), with (x, h) ≥lex (0, 0) → every real x and h within the printed constraint (x < λ, resp. x ≤ λ), in the continuation problem whose only initial outcome is (x, h); reason: the continuation problem and the argument are defined for any incumbent pair (all box wages are ≥ 0, so an incumbent below 0 is beaten by any opened box exactly as one in [0, λ) is); at the states of the source this is the source's statement
-- source:
--   Feldman, Fu, Peng, Tang (2026), One Trap Is Enough: The Structure and Complexity of Robust Contracts for Sequential Search, held STOC 2027 submission (SHA-256 8b684ffb…cf066), Lemma B.8, p. 27 (PDF 28)

import Mathlib
import Definitions.Def_OneTrap_Core_Model
import Definitions.Def_OneTrap_Core_Search
import Definitions.Def_OneTrap_Core_Index

open MeasureTheory

namespace OneTrap.Core

/-- Lemma B.8 (p. 27). Let `B` be a block of known boxes of index `λ`, a positive finite known
index level (§B.1.3), all other remaining boxes (the set
`R \ B`) of lower index. Problem I has incumbent `(λ, h_I)` and remaining boxes `R`; Problem II
has incumbent `(x, h_II)` with `x ≤ λ` and remaining boxes `R` plus a deterministic trap with
output `y`, wage `x_T = w(y) ≥ λ`, residual `h_T = y − w(y)` and cost `x_T − λ`. Then
`P_I ≥ P_II − Δ` with `Δ = max {0, h_T − h_I}` if `x < λ` and
`Δ = max {0, h_T − h_I, h_II − h_I}` if `x = λ`. -/
theorem lemma_B_8 {ι : Type*} [Fintype ι] [DecidableEq ι] (w : ℝ → ℝ) (hw : IsEffContract w)
    (T : ι → Box) (R B : Finset ι) (hBR : B ⊆ R) (lam : ℝ) (hlam : 0 < lam)
    (hB : ∀ i ∈ B, resv w (T i) = ((lam : ℝ) : EReal))
    (hlow : ∀ j ∈ R \ B, resv w (T j) < ((lam : ℝ) : EReal))
    (hI x hII : ℝ) (hx : x ≤ lam) (y : ℝ) (hy : 0 ≤ y) (hxT : lam ≤ w y) :
    Pbell w (Sum.elim T fun _ : Unit => trap w y lam hy hxT) (R.disjSum Finset.univ) x hII -
        (((if x < lam then max 0 (y - w y - hI)
            else max (max 0 (y - w y - hI)) (hII - hI)) : ℝ) : EReal) ≤
      Pbell w T R lam hI := by sorry

end OneTrap.Core
