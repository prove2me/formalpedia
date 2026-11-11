-- Prove2me | Theorems.Thm_OneTrap_Core_lemma_B_3
-- name    : OneTrap.Core.lemma_B_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T02:46:47.510042+00:00
-- url     : https://prove2.me/theorems/fb924660-d23c-4318-85d0-6d1fe7a3e02b
-- title:
--   Lemma B.3 — Weitzman's covered-wage bound with zero costs and infinite indices, attained by the index policy
-- statement:
--   Fix $w\in W_{\mathrm{eff}}$ and a finite technology $A$. Let $x\ge 0$ be the highest currently available wage and $X^{\mathrm{cov}}_i=\min\{X_i,\rho_i\}$. For every policy $\pi$,
--   $$U^x_A(w,\pi)\le\mathbb E\Big[\max\big\{x,\max_{i\in A}X^{\mathrm{cov}}_i\big\}\Big],$$
--   with equality for the policy that opens boxes in nonincreasing order of reservation values and stops once the highest available wage weakly exceeds the largest remaining reservation value. Zero costs and $\rho_i=+\infty$ are allowed.
--
--   Differences from the source:
--   - encoding: a policy assigns to every history (distinct actions with observed outputs) a probability distribution over taking an unopened action or stopping and submitting the null output or an observed output, Borel in the observed outputs → `Policy`: a rule of the opened set S, the outputs y (pre-sampled from the product law) and one seed u uniform on [0, 1] that reads y only on S, is measurable, opens only unopened boxes and submits only available outcomes; reason: the order in which S was opened is itself a function of the rule, y on S and u, and one uniform seed generates independent randomizations for every step (and conversely), so the laws of (opened set, submitted output) are the same
--   - encoding: expected payoffs U_A, P_A in the extended reals (Appendix A) → `eexp`: lower Lebesgue integral of the positive part minus that of the negative part, in EReal; reason: the convention of Appendix A; never the Bochner integral; ⊤ − ⊤ (= ⊥ in EReal) does not arise for these payoffs because the agent payoff is bounded below and the principal payoff above by integrable variables
--   - encoding: ρ_i: the smallest extended-real solution of c_i = E[(X_i − ρ_i)+], with (X − ∞)+ := 0 → `resv w b` = `sInf` in EReal of the r with ∫⁻ ((w y : EReal) − r).toENNReal dF = ofReal c; reason: in EReal, X − ⊤ = ⊥ whose positive part is 0, and X − ⊥ = ⊤; the solution set is closed, so its infimum is its least element when it is nonempty (Lemma B.12)
--   - encoding: U^x_A(w, π): wage x available from the start, all boxes of A unopened → `agentValue w T (fun _ : Unit => (x, h)) π` for `π : Policy Unit univ`, for every residual h; reason: the agent's payoff does not depend on the residual attached to x
--   - encoding: E[max{x, max_{i ∈ A} X^cov_i}] → `eexp` over the product law of `max x (univ.sup X^cov)` in EReal (the inner max is ⊥ for empty A); reason: the empty maximum leaves x
--   - reading: "stopping once the highest available wage weakly exceeds the largest remaining finite reservation value" → `IsIndexPolicy`: stop exactly when the highest available wage is ≥ the largest remaining reservation value, which is +∞ while an infinite-index box remains; reason: the rule of the proof (p. 33: stop otherwise than when the wage is strictly below the largest remaining value) and of §3.1; the literal "finite" reading fails (INSIGHTS.yaml I1)
--   - reading: "Equality is attained by" the index rule → such a policy exists, and every policy following the rule (ties among equal indices broken arbitrarily, an outcome of highest wage submitted) attains equality; reason: the proof shows every such policy attains the bound
--   - encoding: a policy from the state where wage x is available may also stop on the null output (always available; wage w(0) = 0) → the continuation problem offers only the incumbent (x, h) as initial outcome (`fun _ : Unit => (x, h)`), not the null output; reason: w(0) = 0 ≤ x, so a policy that submits the null output is weakly beaten by the same policy submitting the incumbent instead (same costs, wage x ≥ 0); the bound for these policies gives it for all, and the index policies never submit the null output
-- source:
--   Feldman, Fu, Peng, Tang (2026), One Trap Is Enough: The Structure and Complexity of Robust Contracts for Sequential Search, held STOC 2027 submission (SHA-256 8b684ffb…cf066), Lemma B.3, p. 23 (PDF 24)

import Mathlib
import Definitions.Def_OneTrap_Core_Model
import Definitions.Def_OneTrap_Core_Search
import Definitions.Def_OneTrap_Core_Index

open MeasureTheory

namespace OneTrap.Core

/-- Lemma B.3 (p. 23). Let `x ≥ 0` be the highest currently available wage and
`X^cov_i = min {X_i, ρ_i}`. Every policy has `U^x_A(w, π) ≤ E[max {x, max_i X^cov_i}]`, and
equality is attained by opening boxes in nonincreasing order of reservation values and
stopping once the highest available wage weakly exceeds the largest remaining reservation
value. Zero costs and `ρ_i = +∞` are allowed. -/
theorem lemma_B_3 {ι : Type*} [Fintype ι] [DecidableEq ι] (w : ℝ → ℝ) (hw : IsEffContract w)
    (T : ι → Box) (x : ℝ) (hx : 0 ≤ x) (h : ℝ) :
    (∀ π : Policy Unit (Finset.univ : Finset ι),
      agentValue w T (fun _ : Unit => (x, h)) π ≤
        eexp (outputLaw T) fun y =>
          max ((x : ℝ) : EReal) (Finset.univ.sup fun i => coveredWage w (T i) (y i))) ∧
    (∃ π : Policy Unit (Finset.univ : Finset ι), IsIndexPolicy w T x π) ∧
    (∀ π : Policy Unit (Finset.univ : Finset ι), IsIndexPolicy w T x π →
      agentValue w T (fun _ : Unit => (x, h)) π =
        eexp (outputLaw T) fun y =>
          max ((x : ℝ) : EReal) (Finset.univ.sup fun i => coveredWage w (T i) (y i))) := by sorry

end OneTrap.Core
