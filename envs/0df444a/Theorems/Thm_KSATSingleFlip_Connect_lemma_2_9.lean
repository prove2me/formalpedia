-- Prove2me | Theorems.Thm_KSATSingleFlip_Connect_lemma_2_9
-- name    : KSATSingleFlip.Connect.lemma_2_9
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T21:06:27.993227+00:00
-- url     : https://prove2.me/theorems/7b624f81-5d16-4603-85b8-12409e835f0b
-- title:
--   Lemma 2.9 — fixed-assignment to uniform-solution transfer
-- statement:
--   Let $r\in\{1,2\}$. Suppose an event $\mathcal B(\Phi,x_1,\dots,x_r)$, together with any auxiliary randomness, has conditional probability at most $b$ for every fixed ordered $r$-tuple, given that all its assignments satisfy $\Phi$ (whenever this conditioning event has positive probability). Then
--   $$\mathbb E\big[\mathbf 1\{\mathcal Z\}\,\mu_\Phi^{\otimes r}(\mathcal B)\big]\ \le\ \begin{cases} bL_Z, & r = 1,\\ 2bL_Z^2\exp(2\alpha\varepsilon_0(2/3)^k n), & r = 2,\end{cases}$$
--   where the pair bound assumes $\alpha\le 2^k/512$. If instead the hypothesis is for $\mathrm{Pois}(m)$ clauses (integer $m\ge1$) drawn from each fixed tuple's conditional clause law, replace $b$ by $3\sqrt m\,b$.
--
--   In Lean the event with its auxiliary randomness is its conditional probability $f(\Phi,x)\in[0,1]$ over the auxiliary randomness; $\mu_\Phi^{\otimes r}(\mathcal B) = Z_\Phi^{-r}\sum_{x\in\Omega_\Phi^r} f(\Phi,x)$ (zero when $Z_\Phi = 0$). The fixed-count hypothesis reads $\mathbb E[f(\Phi,x)\mathbf 1\{x\subseteq\Omega_\Phi\}]\le b\Pr(x\subseteq\Omega_\Phi)$; the Poissonised one $\mathbb E[f(\Phi',x)]\le b$ for $\Phi'$ made of $\mathrm{Pois}(m)$ clauses uniform among those satisfied by every $x_i$ (when there is such a clause).
--
--   Differences from the source:
--   - reading: no explicit range of k and n in the statement → ∃ k₀, ∀ k ≥ k₀, ∃ n₀, ∀ n ≥ n₀; reason: the model paragraph (p. 2) fixes the standing convention: "All results fix sufficiently large k and then sufficiently large n, uniformly over the stated density range"
--   - encoding: an event B(Φ, x₁, …, x_r) with auxiliary randomness, conditional probability ≤ b given x ⊆ Ω_Φ when that has positive probability → a function f(Φ, x) ∈ [0,1] (the conditional probability over the auxiliary randomness) with E[f·1{x ⊆ Ω_Φ}] ≤ b·Pr(x ⊆ Ω_Φ); reason: the two are equivalent: the product form is the conditional bound when Pr(x ⊆ Ω_Φ) > 0 and is trivial otherwise
--   - encoding: each fixed tuple's conditional clause law → uniform on clausesSatBy xs (the proper k-clauses satisfied by every x_i), required nonempty; reason: a uniform clause conditioned to be satisfied by all x_i is uniform on that set; the law exists iff the set is nonempty
--   - encoding: variables [n] = {1,…,n}, formulas as indexed clause collections → variables Fin n; Φ(k,n,m) = uniform law on the published Formula n k m; other formulas are clause lists (position = clause index), sub-formulas are sets of positions; reason: bijective reindexing; repeated clauses stay distinct, as in the paper's indexed collections
-- source:
--   Wang, Yin, Yu, Zhang (2026), Single-Variable Connectivity in Random k-SAT, arXiv:2611.05981 (held version, SHA-256 1821a501…58b80f5), Lemma 2.9, printed p. 13 (PDF 15)

import Mathlib
import Definitions.Def_SATComputability
import Definitions.Def_KSATSingleFlip_Connect_Model

open scoped Classical BigOperators
open OAI.FixedClauseThreshold

namespace KSATSingleFlip.Connect

/-- Lemma 2.9 (fixed-assignment to uniform-solution transfer; printed p. 13). An event
`B(Φ, x₁, …, x_r)` together with any auxiliary randomness is given by its conditional probability
`f(Φ, x) ∈ [0, 1]` over that auxiliary randomness; `µ_Φ^{⊗r}(B)` is the average of `f(Φ, ·)` over
`r` independent uniform solutions. The fixed-count hypothesis is
`E[f(Φ, x) 1{x ⊆ Ω_Φ}] ≤ b Pr(x ⊆ Ω_Φ)` for every tuple (the conditional bound whenever the
conditioning event has positive probability); the Poissonised hypothesis draws `Pois(m)` clauses
from the tuple's conditional clause law (uniform among clauses satisfied by every `x_i`). -/
theorem lemma_2_9 :
    ∃ k0 : ℕ, ∀ k ≥ k0, ∃ n0 : ℕ, ∀ n ≥ n0, ∀ (m r : ℕ), (r = 1 ∨ r = 2) →
      (r = 2 → (m : ℝ) / n ≤ (2 : ℝ) ^ k / 512) →
      ∀ (f : List (ProperClause n k) → (Fin r → Fin n → Bool) → ℝ),
        (∀ l xs, 0 ≤ f l xs ∧ f l xs ≤ 1) →
      ∀ b : ℝ,
        let transfer : ℝ → ℝ := fun b' =>
          if r = 1 then b' * LZ n k m
          else 2 * b' * LZ n k m ^ 2 *
            Real.exp (2 * ((m : ℝ) / n) * eps0 k * (2 / 3 : ℝ) ^ k * n)
        let lhs : ℝ := uexp fun F : Formula n k m =>
          (if ZEvent F then (1 : ℝ) else 0) *
            ((∑ xs : Fin r → Fin n → Bool,
                if ∀ i, xs i ∈ sols (ofFormula F) then f (List.ofFn F) xs else 0) /
              ((numSols (ofFormula F) : ℝ) ^ r))
        ((∀ xs : Fin r → Fin n → Bool,
            uexp (fun F : Formula n k m =>
              if ∀ i, xs i ∈ sols (ofFormula F) then f (List.ofFn F) xs else 0) ≤
            b * formulaProb n k m (fun F => ∀ i, xs i ∈ sols (ofFormula F))) →
          lhs ≤ transfer b) ∧
        (1 ≤ m →
          (∀ xs : Fin r → Fin n → Bool, (clausesSatBy (k := k) xs).Nonempty →
            poisExp (clausesSatBy (k := k) xs) m (fun l => f l xs) ≤ b) →
          lhs ≤ transfer (3 * Real.sqrt m * b)) := by sorry

end KSATSingleFlip.Connect
