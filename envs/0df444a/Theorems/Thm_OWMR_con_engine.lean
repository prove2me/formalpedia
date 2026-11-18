-- Prove2me | Theorems.Thm_OWMR_con_engine
-- name    : OWMR.con_engine
-- status  : Proved
-- author  : @Ming Hu
-- created : 2026-11-16T12:51:40.605459+00:00
-- url     : https://prove2.me/theorems/b7b3bf24-706d-48f1-aa3b-0ae6ede2e98c
-- title:
--   Pathwise description of $\pi_{\rm con}$: supplier rule, dispatch formula, and the offsets of ordinary requests
-- statement:
--   Fix a network, an initial state $x$, and consolidation choices $c$ with $s_i\le S_i$, $s_0\le S_0$ and initial offsets in $(0,1)$. Let $\mathrm{act}$, $Y$ (supplier position), $\widehat P$ (request positions), $q$ (request sizes) and $A$ (cumulative FIFO allocation of each request) be any functions of the demand path that satisfy the explicit recursions of the statement: activation when all pipelines have arrived and every position is at most its target; $Y_{t+1}=(S_0$ if active and $Y_t\le s_0$, else $Y_t)-\sum_iD_{t,i}$; $\widehat P$ follows each retailer's $(s_i,S_i)$ rule; initial requests $S_i-P_i$ in the first active period and $(s_i,S_i)$ requests afterwards; and $A_{s,i}(t)$ the part of the cumulative supplier arrivals by period $t$ beyond the requests ahead of $(s,i)$, capped at $q_{s,i}$. Then there are offsets $\vartheta_{s,i}\in(0,1)$, depending only on demands before period $s$, such that along every demand path:
--   1. the supplier order of $\pi_{\rm con}$ in period $t$ is $(S_0-Y_t)\mathbf 1_{\{\mathrm{act}_t,\ Y_t\le s_0\}}$;
--   2. while active, the dispatch to retailer $i$ in period $t$ is $\sum_{s\le t}\bigl(\mathrm{Ship}_{s,i}(t)-\mathrm{Ship}_{s,i}(t-1)\bigr)$, with $\mathrm{Ship}$ the shipped quantity of Lemma C.3 at offset $\vartheta_{s,i}$ for batch retailers and the allocation $A$ itself for immediate retailers; before activation the only dispatch is the whole initial warehouse stock to the fixed retailer in period $T_{\rm pipe}-1$;
--   3. for every ordinary request of a batch retailer, $\vartheta_{s,i}$ is the deterministic rule `conRule` of Definition 2 applied to an engine state $\sigma$ at creation and the request's index, and along any continuation of the demands the ideal allocation and ideal depletion of Lemma C.7 from $\sigma$ equal $A_{s,i}(s+k)$ and $\sum_j(S_j-\widehat P_j(s+k))$ for $k\le L_0$.
--
--   So the realized policy is described by explicit processes, and its offsets are the deterministic rule evaluated on the explicit allocation paths.
-- source:
--   M. Hu, "A 5/2 Guarantee for Echelon Stock (s,S) Policies in One-Warehouse Multi-Retailer Systems", working paper (manuscript of November 2026), Section 6, Definition 2, p. 27; Appendix C, Step 2 (policy and allocation, (C.7)-(C.11)), pp. E.10-E.12, Step 7 (offset selection), p. E.20, and Step 8 (initialization), pp. E.21-E.22.

import Definitions.Def_owmr_consolidation_policy

open MeasureTheory
open scoped ENNReal NNReal

namespace OWMR
theorem con_engine {n : ℕ} (N : Network n) (x : InitState n) (c : ConChoice n)
    (hsS : ∀ i, c.s i ≤ c.S i) (hs0S : c.s0 ≤ c.S0)
    (hθ0 : ∀ i, 0 < c.initOffset i ∧ c.initOffset i < 1)
    (act : (ℕ → DemandVec n) → ℕ → Prop) [∀ d, DecidablePred (act d)]
    (hact : ∀ d t, act d t ↔ (N.Tpipe - 1 + max 1 (N.L c.sendTo) ≤ t ∧ ∀ i,
      x.I i + ∑ s ∈ Finset.range (N.L i), x.retPipe i s
        + (if i = c.sendTo then x.W + ∑ s ∈ Finset.range N.L0, x.supPipe s else 0)
        - ∑ s ∈ Finset.range t, ((d s i : ℝ≥0) : ℝ) ≤ c.S i))
    (Yp : (ℕ → DemandVec n) → ℕ → ℝ)
    (hY0 : ∀ d, Yp d 0 = x.W + ∑ s ∈ Finset.range N.L0, x.supPipe s
      + ∑ i, (x.I i + ∑ s ∈ Finset.range (N.L i), x.retPipe i s - c.S i))
    (hY : ∀ d t, Yp d (t + 1) = (if act d t ∧ Yp d t ≤ c.s0 then c.S0 else Yp d t)
      - ∑ i, ((d t i : ℝ≥0) : ℝ))
    (Ph : (ℕ → DemandVec n) → ℕ → Fin n → ℝ)
    (hPh0 : ∀ d i, Ph d 0 i = c.S i)
    (hPh : ∀ d t i, Ph d (t + 1) i = if act d t then
      (if Ph d t i - ((d t i : ℝ≥0) : ℝ) ≤ c.s i then c.S i else Ph d t i - ((d t i : ℝ≥0) : ℝ))
      else c.S i)
    (q : (ℕ → DemandVec n) → ℕ → Fin n → ℝ)
    (hq : ∀ d t i, q d t i = if act d t then
      (if t = 0 ∨ ¬ act d (t - 1) then
        c.S i - (x.I i + ∑ s ∈ Finset.range (N.L i), x.retPipe i s
          + (if i = c.sendTo then x.W + ∑ s ∈ Finset.range N.L0, x.supPipe s else 0)
          - ∑ s ∈ Finset.range t, ((d s i : ℝ≥0) : ℝ))
      else if Ph d (t - 1) i - ((d (t - 1) i : ℝ≥0) : ℝ) ≤ c.s i then
        c.S i - (Ph d (t - 1) i - ((d (t - 1) i : ℝ≥0) : ℝ)) else 0)
      else 0)
    (A : (ℕ → DemandVec n) → ℕ → Fin n → ℕ → ℝ)
    (hA : ∀ d s i t, A d s i t = max 0 (min (q d s i)
      (∑ r ∈ Finset.range (t + 1 - N.L0), (if act d r ∧ Yp d r ≤ c.s0 then c.S0 - Yp d r else 0)
        - (∑ r ∈ Finset.range s, ∑ j, q d r j + ∑ j ∈ Finset.univ.filter (· < i), q d s j)))) :
    ∃ θ : (ℕ → DemandVec n) → ℕ → Fin n → ℝ,
      (∀ d s i, 0 < θ d s i ∧ θ d s i < 1) ∧
      (∀ d d' s, (∀ r < s, d r = d' r) → ∀ i, θ d s i = θ d' s i) ∧
      (∀ d t, (conPolicy N x c).order t d
        = if act d t ∧ Yp d t ≤ c.s0 then c.S0 - Yp d t else 0) ∧
      (∀ d t i, (conPolicy N x c).dispatch t d i = if act d t then
        ∑ s ∈ Finset.range (t + 1),
          ((if c.batch i then shippedPath (q d s i) (θ d s i) (fun k => A d s i (s + k)) (t - s)
              else A d s i t)
            - if s < t then (if c.batch i then
                shippedPath (q d s i) (θ d s i) (fun k => A d s i (s + k)) (t - 1 - s)
              else A d s i (t - 1)) else 0)
        else if t = N.Tpipe - 1 ∧ i = c.sendTo then x.W + ∑ s ∈ Finset.range N.L0, x.supPipe s
        else 0) ∧
      (∀ d s i, 0 < s → act d (s - 1) → 0 < q d s i → c.batch i = true →
        ∃ σ : EngState n,
          θ d s i = conRule N c σ s (∑ r ∈ Finset.range s,
              (if 0 < r ∧ act d (r - 1) then
                ((List.finRange n).filter (fun j => decide (0 < q d r j))).length else 0)
            + ((List.finRange n).filter (fun j => decide (0 < q d s j))).idxOf i + 1) i (q d s i) ∧
          ∀ (ds : Fin N.L0 → DemandVec n) (k : ℕ), k ≤ N.L0 →
            idealAlloc N c.params σ s i (q d s i) (padHist N.L0 ds) k = A d s i (s + k) ∧
            idealDepletion N c.params σ s (padHist N.L0 ds) k
              = ∑ j, (c.S j - Ph (fun r => if r < s then d r else padHist N.L0 ds (r - s)) (s + k) j)) := by sorry
end OWMR
