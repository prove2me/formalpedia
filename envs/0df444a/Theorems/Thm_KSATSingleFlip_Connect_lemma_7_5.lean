-- Prove2me | Theorems.Thm_KSATSingleFlip_Connect_lemma_7_5
-- name    : KSATSingleFlip.Connect.lemma_7_5
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T21:08:30.553119+00:00
-- url     : https://prove2.me/theorems/deedcdf3-161f-4976-a8eb-8a6bfe9b0a77
-- title:
--   Lemma 7.5 — correctness of FindPath
-- statement:
--   Let $(U,t)$ be an $(x,W)$-repair and $\Phi\subseteq\Phi^+$. For $y,y'\in\Omega_\Phi$ agreeing with $x$ outside $U$, $\mathrm{FindPath}(y,y',t)$ (Algorithm 4) returns a satisfying path from $y$ to $y'$ in $\Omega_\Phi$ of length $d_H(y,t)+d_H(y',t)\le2|U|$ in $O_k(n(n+|\Phi|))$ time.
--
--   Differences from the source:
--   - encoding: O_k(n(n + |Φ|)) time → ∃ C_k > 0 (after k): findPathCost ≤ C_k n (n + |Φ|); reason: the paper gives no machine model; the cost model charges one clause scan per flip and n per written assignment, the paper's own accounting (p. 66)
--   - encoding: γ_y ∘ rev(γ_{y′}) → the concatenation listing the shared endpoint t once; reason: a path cannot repeat an assignment consecutively; the length d_H(y,t) + d_H(y′,t) is the source's
--   - encoding: any k → k ≥ 1; reason: a 0-clause is not a k-SAT clause
--   - encoding: Φ ⊆ Φ⁺ → a set I of positions of the clause list Φ⁺; reason: sub-multisets of an indexed collection
--   - encoding: variables [n] = {1,…,n}, formulas as indexed clause collections → variables Fin n; Φ(k,n,m) = uniform law on the published Formula n k m; other formulas are clause lists (position = clause index), sub-formulas are sets of positions; reason: bijective reindexing; repeated clauses stay distinct, as in the paper's indexed collections
-- source:
--   Wang, Yin, Yu, Zhang (2026), Single-Variable Connectivity in Random k-SAT, arXiv:2611.05981 (held version, SHA-256 1821a501…58b80f5), Lemma 7.5, printed p. 54 (PDF 56)

import Mathlib
import Definitions.Def_SATComputability
import Definitions.Def_KSATSingleFlip_Connect_Model
import Definitions.Def_KSATSingleFlip_Connect_FactorGraph
import Definitions.Def_KSATSingleFlip_Connect_Repair

open scoped Classical BigOperators
open OAI.FixedClauseThreshold

namespace KSATSingleFlip.Connect

/-- Lemma 7.5 (correctness of FindPath; printed p. 54). Let `(U, t)` be an `(x, W)`-repair for `Φ⁺`
and `Φ ⊆ Φ⁺` (positions `I`). For `y, y′ ∈ Ω_Φ` agreeing with `x` outside `U`, FindPath(y, y′, t)
(Algorithm 4) returns a satisfying path from `y` to `y′` in `Ω_Φ` of length
`d_H(y, t) + d_H(y′, t) ≤ 2|U|`, at cost at most `C_k n (n + |Φ|)` in the declared cost model
(`findPathCost`), with `C_k` depending only on `k`. -/
theorem lemma_7_5 :
    ∀ k : ℕ, 1 ≤ k → ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (Φp : List (ProperClause n k))
      (x : Fin n → Bool) (W U : Finset (Fin n)) (t : Fin n → Bool),
      IsRepair (ofList Φp) x W U t →
      ∀ (I : Finset (Fin (ofList Φp).length)) (y y' : Fin n → Bool),
        y ∈ sols (subF (ofList Φp) I) → y' ∈ sols (subF (ofList Φp) I) →
        (∀ u, u ∉ U → y u = x u) → (∀ u, u ∉ U → y' u = x u) →
          ∃ p, findPath (subF (ofList Φp) I) y y' t = some p ∧
            IsSatPath (subF (ofList Φp) I) p y y' ∧
            pathLength p = hamming y t + hamming y' t ∧
            hamming y t + hamming y' t ≤ 2 * U.card ∧
            (findPathCost n (subF (ofList Φp) I).length p : ℝ) ≤
              C * n * (n + (subF (ofList Φp) I).length) := by sorry

end KSATSingleFlip.Connect
