-- Prove2me | Theorems.Thm_KSATSingleFlip_Connect_lemma_7_6
-- name    : KSATSingleFlip.Connect.lemma_7_6
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T21:07:33.678743+00:00
-- url     : https://prove2.me/theorems/774b53af-b173-4aea-b6fc-dddaef02645a
-- title:
--   Lemma 7.6 — formula regularity: $\Pr(\mathsf{Reg}(\Phi)^c)\le n^{-4}$
-- statement:
--   For sufficiently large $k$ there is a degree cutoff $D_k$ (depending only on $k$; Definition 7.2) such that for $n\ge n_0(k)$, if $\Phi$ consists of at most $2^k n$ clauses on $[n]$ with independent uniform scopes, then $\Pr(\mathsf{Reg}(\Phi)^c)\le n^{-4}$. Here $\mathsf{Reg} = \mathsf{LT}\cap\mathsf{LS}$ with $\rho = k^{-100\lceil(\ln k)^6\rceil}$, $\eta = (\ln k)^{10}/(64k)$: $\mathsf{LT}$ — at least $(1-\eta)n$ variables are $(2k+4,D_k)$-locally tree-structured; $\mathsf{LS}$ — $|\{C:\mathrm{vbl}(C)\subseteq A\}|<2|A|/k$ for all $0<|A|\le\rho n$.
--
--   Differences from the source:
--   - encoding: at most 2^k n clauses with independent uniform scopes (signs unspecified) → ∀ M ≤ 2^k n, Φ uniform on Formula n k M (fair signs); reason: Reg depends only on the scopes, so the signs are immaterial
--   - encoding: D_k chosen in the proof, depending only on k → ∃ D after k, before n₀; reason: the paper's existential choice, at its level
--   - encoding: variables [n] = {1,…,n}, formulas as indexed clause collections → variables Fin n; Φ(k,n,m) = uniform law on the published Formula n k m; other formulas are clause lists (position = clause index), sub-formulas are sets of positions; reason: bijective reindexing; repeated clauses stay distinct, as in the paper's indexed collections
-- source:
--   Wang, Yin, Yu, Zhang (2026), Single-Variable Connectivity in Random k-SAT, arXiv:2611.05981 (held version, SHA-256 1821a501…58b80f5), Lemma 7.6 (with Definition 7.2), printed p. 54 (PDF 56)

import Mathlib
import Definitions.Def_SATComputability
import Definitions.Def_KSATSingleFlip_Connect_Model
import Definitions.Def_KSATSingleFlip_Connect_FactorGraph

open scoped Classical BigOperators
open OAI.FixedClauseThreshold

namespace KSATSingleFlip.Connect

/-- Lemma 7.6 (formula regularity; printed p. 54). For sufficiently large `k` there is a degree
cutoff `D_k` (Definition 7.2; it depends only on `k`) such that for `n ≥ n₀(k)`, a formula of at
most `2^k n` clauses with independent uniform scopes is regular except with probability at most
`n^{−4}`. (`Reg` depends only on the scopes, so the signs are immaterial; they are drawn fair.) -/
theorem lemma_7_6 :
    ∃ k0 : ℕ, ∀ k ≥ k0, ∃ D : ℕ, ∃ n0 : ℕ, ∀ n ≥ n0, ∀ M : ℕ, (M : ℝ) ≤ (2 : ℝ) ^ k * n →
      formulaProb n k M (fun F => ¬ Reg k D (ofFormula F)) ≤ 1 / (n : ℝ) ^ 4 := by sorry

end KSATSingleFlip.Connect
