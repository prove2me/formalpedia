-- Prove2me | Theorems.Thm_HiringLP_SimLower_lemma_12
-- name    : HiringLP.SimLower.lemma_12
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T09:02:33.116006+00:00
-- url     : https://prove2.me/theorems/e49a713b-e0b3-4953-9e0b-751bd801dbd7
-- title:
--   Lemma 12 — the total mass of an optimal prefix solution is P_high if P_high > k, and min{k, P_total} otherwise
-- statement:
--   Let $I=(k,n,p,v)$ be a valid Simultaneous Offering instance and assume moreover that
--   $$v_i>0,\qquad v_i\ne 1,\qquad p_i>0\qquad\text{for every } i\in[n].$$
--   Let $(y,z)$ be an optimal solution of $\mathrm{LP}_{\mathrm{sim}}(I)$ with the structure of Lemma 11, and let $P_{\mathrm{high}}=\sum_{i\in V_{\mathrm{high}}}p_i$, $P_{\mathrm{total}}=\sum_{i\in[n]}p_i$. Then:
--   1. if $P_{\mathrm{high}}>k$, then $y_i=1$ for all $i\in V_{\mathrm{high}}$ and $y_i=0$ otherwise; therefore $\sum_{i}y_ip_i=P_{\mathrm{high}}$;
--   2. if $P_{\mathrm{high}}\le k$, then $\sum_i y_ip_i=\min\{k,P_{\mathrm{total}}\}$.
--
--   The lemma identifies the total mass of the LP optimum, which is all the algorithm $\mathrm{ALG}^s_{\mathrm{sim}}$ uses, and splits the analysis into the two cases of Lemmas 13 and 14.
--
--   **Formalization Note** The hypothesis $v_i>0,\ v_i\ne1,\ p_i>0$ is an addition to the paper's statement, which is false without it: with $k=1$, $v=(1,1)$, $p=(1,1)$, the solution $y=(1,1)$, $z=-1$ is optimal with the Lemma 11 structure but has mass $2\ne\min\{k,P_{\mathrm{total}}\}=1$; with $k=1$, $v=(2,2,1)$, $p=(1,1,1)$, $y=(1,1,1)$ is optimal although $P_{\mathrm{high}}=2>k$; with $k=2$, $v=(\tfrac12,0)$, $p=(1,1)$, $y=(1,0)$ is optimal with mass $1\ne 2$; with $k=1$, $v=(2,2,\tfrac12)$, $p=(1,1,0)$, $y=(1,1,1)$ is optimal and violates "$y_i=0$ otherwise". Under the hypothesis the optimal solution with the Lemma 11 structure is unique. Indices are 0-based.
-- source:
--   Epstein, Ma, Selection and Ordering Policies for Hiring Pipelines via Linear Programming, arXiv:2210.04059v3, p. 28, Lemma 12

import Mathlib
import Definitions.Def_HiringLP_SimLower_Model
import Definitions.Def_HiringLP_SimLower_LP

open Finset

namespace HiringLP.SimLower

/-- Lemma 12 (p. 28), under the disclosed hypothesis `0 < vᵢ`, `vᵢ ≠ 1`, `0 < pᵢ` for all `i` (without it
the statement fails, see the Formalization Note): an optimal solution with the Lemma 11 structure has
total mass `P_high` (and is the indicator of `V_high`) when `P_high > k`, and total mass
`min{k, P_total}` when `P_high ≤ k`. -/
theorem lemma_12 {n : ℕ} (I : SimInstance n) (hI : I.Valid)
    (hgen : ∀ i, 0 < I.v i ∧ I.v i ≠ 1 ∧ 0 < I.p i)
    (y : Fin n → ℝ) (z : ℝ) (hopt : IsLPOpt I y z) (j : Fin n) (hpre : IsPrefix y j) :
    ((I.k : ℝ) < Phigh I →
        (∀ i, y i = if i ∈ Vhigh I then 1 else 0) ∧ ∑ i, y i * I.p i = Phigh I) ∧
      (Phigh I ≤ I.k → ∑ i, y i * I.p i = min (I.k : ℝ) (Ptotal I)) := by sorry

end HiringLP.SimLower
