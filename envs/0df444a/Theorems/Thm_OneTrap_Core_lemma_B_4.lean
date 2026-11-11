-- Prove2me | Theorems.Thm_OneTrap_Core_lemma_B_4
-- name    : OneTrap.Core.lemma_B_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T02:46:55.763541+00:00
-- url     : https://prove2.me/theorems/e53da691-1e9c-4696-8caa-8e81866c5611
-- title:
--   Lemma B.4 — index locality: stop above the largest remaining index; delete lower-index boxes at equality
-- statement:
--   Fix $w\in W_{\mathrm{eff}}$. At any state $(R,x,h)$ with $R\ne\emptyset$: if $x>\max_{i\in R}\rho_i$, immediate stopping is a principal-favored optimal decision and $U(R,x,h)=x$, $P(R,x,h)=h$; if $x=\max_{i\in R}\rho_i$, deleting every box $i\in R$ with $\rho_i<x$ leaves both $U$ and $P$ unchanged.
--
--   Differences from the source:
--   - encoding: U(R, x, h) and P(R, x, h): the agent's optimal value from the state and the best principal value among the policies attaining it → `Ubell`/`Pbell`: the optimal values of the search problem whose openable boxes are R and whose only initially available outcome is (x, h) (agent value as a supremum over policies, principal value as `pfValue`); reason: stopping yields exactly (x, h), as u_stop = x and p_stop = h in (17); earlier outcomes are lexicographically below the incumbent and the remaining outputs are independent of the past
--   - generalization: states (R, x, h) that arise in the search: x the highest observed wage, h the largest residual at wage x (so (x, h) ≥lex (0, 0)) → every finite R ⊆ A and every real x and h; reason: the continuation problem and the argument are defined for any incumbent pair; at the states of the source this is the source's statement
--   - encoding: immediate stopping is a PF-optimal decision → every policy that at the start stops on the incumbent is agent-optimal and attains P(R, x, h); reason: this is PF-optimality of that decision
--   - encoding: max_{i ∈ R} ρ_i → `R.sup' hR ρ` in EReal; reason: R is nonempty
-- source:
--   Feldman, Fu, Peng, Tang (2026), One Trap Is Enough: The Structure and Complexity of Robust Contracts for Sequential Search, held STOC 2027 submission (SHA-256 8b684ffb…cf066), Lemma B.4, p. 23 (PDF 24)

import Mathlib
import Definitions.Def_OneTrap_Core_Model
import Definitions.Def_OneTrap_Core_Search
import Definitions.Def_OneTrap_Core_Index

open MeasureTheory

namespace OneTrap.Core

/-- Lemma B.4 (p. 23). At a state `(R, x, h)` with `R ≠ ∅`: if `x > max_{i ∈ R} ρ_i`, immediate
stopping is principal-favored optimal and `U(R, x, h) = x`, `P(R, x, h) = h`; if
`x = max_{i ∈ R} ρ_i`, deleting every box of `R` with `ρ_i < x` changes neither `U` nor `P`. -/
theorem lemma_B_4 {ι : Type*} [Fintype ι] [DecidableEq ι] (w : ℝ → ℝ) (hw : IsEffContract w)
    (T : ι → Box) (R : Finset ι) (hR : R.Nonempty) (x h : ℝ) :
    (R.sup' hR (fun i => resv w (T i)) < ((x : ℝ) : EReal) →
      (∀ π : Policy Unit R,
        (∀ (y : ι → ℝ) (u : ℝ), (π.rule ∅ y u).submitted? = some (Sum.inl ())) →
          π ∈ agentOptimal w T R (fun _ : Unit => (x, h)) ∧
          principalValue w T (fun _ : Unit => (x, h)) π = Pbell w T R x h) ∧
      Ubell w T R x h = ((x : ℝ) : EReal) ∧ Pbell w T R x h = ((h : ℝ) : EReal)) ∧
    (((x : ℝ) : EReal) = R.sup' hR (fun i => resv w (T i)) →
      Ubell w T (R.filter fun i => ¬ resv w (T i) < ((x : ℝ) : EReal)) x h = Ubell w T R x h ∧
      Pbell w T (R.filter fun i => ¬ resv w (T i) < ((x : ℝ) : EReal)) x h = Pbell w T R x h) := by sorry

end OneTrap.Core
