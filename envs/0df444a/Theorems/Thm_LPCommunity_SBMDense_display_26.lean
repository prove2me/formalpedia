-- Prove2me | Theorems.Thm_LPCommunity_SBMDense_display_26
-- name    : LPCommunity.SBMDense.display_26
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T12:37:35.319246+00:00
-- url     : https://prove2.me/theorems/de4996de-ff2e-4d1d-b054-50d3ad3129c6
-- title:
--   (26), p. 16 — in the SBM the fraction of edges across the planted bisection concentrates at q/(p+q)
-- statement:
--   Let $p=p(n)$ and $q=q(n)$ be edge probabilities with $p,q=\Omega(\log n/n)$, i.e. $p(n),q(n)\ge c\log n/n$ for some constant $c>0$ and all large $n$, with $p(n),q(n)\le 1$ for all large $n$, and such that $\lim_{n\to\infty}q/p$ exists and lies in $(0,1]$. Let $(V_1,G)\sim\mathcal G_{n,p,q}$, $n$ even, and let $E$ be the edge set of $G$ and $E_0$ the set of its edges between $V_1$ and $V_2$. Then for every $\epsilon>0$,
--
--   $$
--   \lim_{n\to\infty}\mathbb P\Big[(1-\epsilon)\frac{q}{p+q}\le\frac{|E_0|}{|E|}\le(1+\epsilon)\frac{q}{p+q}\Big]=1.
--   $$
--
--   This is the first step of the proof of Theorem 7: by Theorem 5 the LP fails whenever $|E_0|/|E|$ exceeds the quantity $b(G)$ of (27), and (26) identifies the left side asymptotically. The same display is used for the logarithmic-degree regime (Theorem 8); for $p=\alpha s(n)$, $q=\beta s(n)$ the threshold is the constant $\beta/(\alpha+\beta)$.
--
--   **Formalization Note** The paper writes "$\lim p/q$ existing and taking a value in $(0,1]$"; with the SBM's standing assumption $p>q$ the ratio meant is $q/p$ (a printed slip), and that is the hypothesis posed. The hypothesis $p,q\le1$ eventually only says that $p,q$ are probabilities (the model clamps them into $[0,1]$). $p$ and $q$ are sequences indexed by $n$, and the limit runs over even $n=2m$; the threshold $q/(p+q)$ is evaluated at the same $n$. If $G$ has no edge the ratio is read as $0$.
-- source:
--   Del Pia, Khajavirad, Kunisky, Linear Programming and Community Detection, arXiv:2006.03213v2, p. 16, proof of Theorem 7, display (26)

import Mathlib
import Definitions.Def_LPCommunity_MinBisect_Setting
import Definitions.Def_LPCommunity_SBMRecovery_Setting

open scoped Classical

namespace LPCommunity.SBMDense

theorem display_26 (p q : ℕ → ℝ)
    (hpq : ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in Filter.atTop,
      c * Real.log n / n ≤ p n ∧ c * Real.log n / n ≤ q n)
    (hpq1 : ∀ᶠ n : ℕ in Filter.atTop, p n ≤ 1 ∧ q n ≤ 1)
    (r : ℝ) (hr0 : 0 < r) (hr1 : r ≤ 1)
    (hlim : Filter.Tendsto (fun n : ℕ => q n / p n) Filter.atTop (nhds r))
    (ε : ℝ) (hε : 0 < ε) :
    Filter.Tendsto
      (fun m : ℕ => LPCommunity.SBMRecovery.sbmProb (2 * m) (p (2 * m)) (q (2 * m))
        (fun V1 G =>
          (1 - ε) * (q (2 * m) / (p (2 * m) + q (2 * m))) ≤
              (LPCommunity.MinBisect.cutCost G V1 : ℝ) / (G.edgeFinset.card : ℝ) ∧
            (LPCommunity.MinBisect.cutCost G V1 : ℝ) / (G.edgeFinset.card : ℝ) ≤
              (1 + ε) * (q (2 * m) / (p (2 * m) + q (2 * m)))))
      Filter.atTop (nhds 1) := by sorry

end LPCommunity.SBMDense
