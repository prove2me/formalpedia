-- Prove2me | Theorems.Thm_OneTrap_Core_lemma_B_6
-- name    : OneTrap.Core.lemma_B_6
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T02:46:29.177298+00:00
-- url     : https://prove2.me/theorems/d37a9767-b642-4ee3-8a81-5bc32e5617a5
-- title:
--   Lemma B.6 — continuation-locality of an equal-index block: one deterministic within-block policy serves every incoming pair below $\lambda$ and every lower-index continuation
-- statement:
--   Fix $w\in W_{\mathrm{eff}}$. Let $B$ be a finite block of boxes with common finite index $\lambda>0$, entered with current highest wage $x<\lambda$, every other remaining box having index strictly below $\lambda$. There is a deterministic principal-favored within-block policy $\pi^\star_B$ that depends only on the boxes in $B$ and the outcomes observed within the block; the same policy applies for every incoming wage–residual pair $(x,h)$ with $x<\lambda$ and every lower-index continuation.
--
--   Differences from the source:
--   - encoding: a policy assigns to every history (distinct actions with observed outputs) a probability distribution over taking an unopened action or stopping and submitting the null output or an observed output, Borel in the observed outputs → `Policy`: a rule of the opened set S, the outputs y (pre-sampled from the product law) and one seed u uniform on [0, 1] that reads y only on S, is measurable, opens only unopened boxes and submits only available outcomes; reason: the order in which S was opened is itself a function of the rule, y on S and u, and one uniform seed generates independent randomizations for every step (and conversely), so the laws of (opened set, submitted output) are the same
--   - encoding: U(R, x, h) and P(R, x, h): the agent's optimal value from the state and the best principal value among the policies attaining it → `Ubell`/`Pbell`: the optimal values of the search problem whose openable boxes are R and whose only initially available outcome is (x, h) (agent value as a supremum over policies, principal value as `pfValue`); reason: stopping yields exactly (x, h), as u_stop = x and p_stop = h in (17); earlier outcomes are lexicographically below the incumbent and the remaining outputs are independent of the past
--   - encoding: a within-block policy π⋆_B → σ : Finset ι → (ι → ℝ) → Option ι: at opened set S it opens σ S y ∈ B \ S or leaves the block (none); it reads y only on S and is measurable; deterministic (no seed); reason: a deterministic rule on within-block histories
--   - reading: π⋆_B depends only on the boxes in B and the within-block outcomes, is principal-favored, and applies for every (x, h) with x < λ and every lower-index continuation → σ is chosen before the technology outside B (any T' equal to T on B), any remaining set R ⊇ B whose other boxes have index < λ, and any (x, h) with x < λ; for each of them some PF-optimal policy from (R, x, h) follows σ at every within-block opened set S ⊆ B and opens no box of B where σ leaves; reason: this is what "depends only on B" and "the same policy applies" assert
--   - generalization: the incumbent wage x of a state: the highest observed wage, so x ≥ 0 (the null output pays w(0) = 0), with (x, h) ≥lex (0, 0) → every real x and h within the printed constraint (x < λ, resp. x ≤ λ), in the continuation problem whose only initial outcome is (x, h); reason: the continuation problem and the argument are defined for any incumbent pair (all box wages are ≥ 0, so an incumbent below 0 is beaten by any opened box exactly as one in [0, λ) is); at the states of the source this is the source's statement
-- source:
--   Feldman, Fu, Peng, Tang (2026), One Trap Is Enough: The Structure and Complexity of Robust Contracts for Sequential Search, held STOC 2027 submission (SHA-256 8b684ffb…cf066), Lemma B.6, p. 24 (PDF 25); recursion (18), p. 25 (PDF 26)

import Mathlib
import Definitions.Def_OneTrap_Core_Model
import Definitions.Def_OneTrap_Core_Search
import Definitions.Def_OneTrap_Core_Index

open MeasureTheory

namespace OneTrap.Core

/-- Lemma B.6 (p. 24), continuation-locality of an equal-index block. Let `B` be a finite block
of boxes with common finite index `λ > 0`. There is a deterministic within-block policy `σ`
(a measurable rule of the within-block observations that opens an unopened box of `B` or
leaves the block) such that, whatever the boxes outside `B`, for every remaining set `R ⊇ B`
whose other boxes have index `< λ` and every incoming pair `(x, h)` with `x < λ`, some
principal-favored optimal policy from `(R, x, h)` processes `B` with `σ` before any other box. -/
theorem lemma_B_6 {ι : Type*} [Fintype ι] [DecidableEq ι] (w : ℝ → ℝ) (hw : IsEffContract w)
    (T : ι → Box) (B : Finset ι) (lam : ℝ) (hlam : 0 < lam)
    (hB : ∀ i ∈ B, resv w (T i) = ((lam : ℝ) : EReal)) :
    ∃ σ : Finset ι → (ι → ℝ) → Option ι,
      (∀ (S : Finset ι) (y : ι → ℝ) (i : ι), σ S y = some i → i ∈ B ∧ i ∉ S) ∧
      (∀ (S : Finset ι) (y y' : ι → ℝ), (∀ i ∈ S, y i = y' i) → σ S y = σ S y') ∧
      (∀ (S : Finset ι) (o : Option ι), MeasurableSet {y : ι → ℝ | σ S y = o}) ∧
      ∀ T' : ι → Box, (∀ i ∈ B, T' i = T i) →
      ∀ R : Finset ι, B ⊆ R → (∀ j ∈ R \ B, resv w (T' j) < ((lam : ℝ) : EReal)) →
      ∀ x h : ℝ, x < lam →
        ∃ π ∈ agentOptimal w T' R (fun _ : Unit => (x, h)),
          principalValue w T' (fun _ : Unit => (x, h)) π = Pbell w T' R x h ∧
          ∀ S : Finset ι, S ⊆ B → ∀ (y : ι → ℝ) (u : ℝ),
            (∀ i, σ S y = some i → (π.rule S y u).box? = some i) ∧
            (σ S y = none → ∀ i ∈ B, (π.rule S y u).box? ≠ some i) := by sorry

end OneTrap.Core
