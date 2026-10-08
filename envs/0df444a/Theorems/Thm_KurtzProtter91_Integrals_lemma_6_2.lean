-- Prove2me | Theorems.Thm_KurtzProtter91_Integrals_lemma_6_2
-- name    : KurtzProtter91.Integrals.lemma_6_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T13:06:29.421117+00:00
-- url     : https://prove2.me/theorems/5f0aa25c-817b-4922-82bb-c1a771af417a
-- title:
--   Lemma 6.2 — sequential characterization of Skorohod convergence (C6.2(i)–(ii))
-- statement:
--   Let $(E',r')$ be a metric space and let $v_n,v$ be cadlag paths in $E'$. Then $v_n\to v$ in the Skorohod topology on $D_{E'}[0,\infty)$ if and only if the following two conditions hold:
--
--   1. (C6.2(i)) if $t_n\to t$, then $\displaystyle\lim_{n\to\infty} r'(v_n(t_n),v(t))\wedge r'(v_n(t_n),v(t-))=0$;
--   2. (C6.2(ii)) if $s_n\ge t_n$, $s_n,t_n\to t$ and $v_n(t_n)\to v(t)$, then $v_n(s_n)\to v(t)$.
--
--   This is Proposition 3.6.5 of Ethier and Kurtz (1986), whose third condition the paper notes is implied by the other two; it is the tool for proving Lemma 6.1.
--
--   **Formalization Note** The sequences $t_n,s_n$ take values in $[0,\infty)$; at $t=0$ the convention $v(0-)=v(0)$ applies.
-- source:
--   Kurtz and Protter, Weak Limit Theorems for Stochastic Integrals and Stochastic Differential Equations, Ann. Probab. 19 (1991), p. 1067, Lemma 6.2

import Mathlib
import Definitions.Def_KurtzProtter91_Integrals_Skorohod

open Filter Topology
open scoped NNReal ENNReal

namespace KurtzProtter91.Integrals

theorem lemma_6_2 {E' : Type*} [MetricSpace E'] (vs : ℕ → ℝ≥0 → E') (v : ℝ≥0 → E')
    (hvs : ∀ n, IsCadlag (vs n)) (hv : IsCadlag v) :
    SkorohodTendsto vs v ↔
      (∀ (ts : ℕ → ℝ≥0) (t : ℝ≥0), Tendsto ts atTop (𝓝 t) →
          Tendsto (fun n => min (dist (vs n (ts n)) (v t)) (dist (vs n (ts n)) (leftLim v t)))
            atTop (𝓝 0)) ∧
      (∀ (ss ts : ℕ → ℝ≥0) (t : ℝ≥0), (∀ n, ts n ≤ ss n) → Tendsto ss atTop (𝓝 t) →
          Tendsto ts atTop (𝓝 t) → Tendsto (fun n => vs n (ts n)) atTop (𝓝 (v t)) →
          Tendsto (fun n => vs n (ss n)) atTop (𝓝 (v t))) := by sorry

end KurtzProtter91.Integrals
