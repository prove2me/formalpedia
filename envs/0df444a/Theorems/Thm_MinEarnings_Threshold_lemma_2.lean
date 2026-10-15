-- Prove2me | Theorems.Thm_MinEarnings_Threshold_lemma_2
-- name    : MinEarnings.Threshold.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T04:30:14.693957+00:00
-- url     : https://prove2.me/theorems/eafc59f1-63b3-4ae7-b318-9c7d40916375
-- title:
--   Lemma 2, p. 9 — unique and continuous equilibrium earnings
-- statement:
--   Under the paper's standing regularity assumptions, for a nonnegative price $p$ and positive wage $w$, equilibrium earnings $z$ are the unique positive solution of $z=w,u(p,z)$. Their value is the continuous function
--
--   $$f(p,w)=\begin{cases}w,&S(w)<D(p),\\H(wD(p)),&S(w)\ge D(p),\end{cases}$$
--
--   where $H$ inverts the labor cost $C(z)=zS(z)$ for positive cost. Continuity holds jointly in $p$ and $w$ on $[0,\infty)\times(0,\infty)$.
--
--   This formula allows policies to be specified by prices and wages while earnings follow from equilibrium.
--
--   **Formalization Note** The paper writes the branch test as $w<S^{-1}(D(p))$; $S(w)<D(p)$ agrees whenever that inverse exists and remains defined if $D(p)$ lies outside the range of $S$. The positive wage and earnings domain excludes $0/0$ in utilization when $S(0)=0$. Supply differentiability is used only at positive earnings.
-- source:
--   Asadpour, Lobel & van Ryzin, Minimum Earnings Regulation and the Stability of Marketplaces, SSRN 3502607 (version of August 24, 2022), p. 9, Lemma 2 and (6); proof Online Appendix pp. 1–2 (PDF 29–30)

import Mathlib
import Definitions.Def_MinEarnings_Threshold_Setting

namespace MinEarnings.Threshold

theorem lemma_2 (D S H : ℝ → ℝ) (pStar wStar : ℝ)
    (hA : Assumptions D S pStar wStar)
    (hH : IsCostInverse S H) :
    (∀ p w : ℝ, 0 ≤ p → 0 < w →
      (0 < eqEarnings D S H p w ∧
        eqEarnings D S H p w = w * util D S p (eqEarnings D S H p w)) ∧
      ∀ z : ℝ, 0 < z → z = w * util D S p z → z = eqEarnings D S H p w) ∧
    ContinuousOn (fun q : ℝ × ℝ => eqEarnings D S H q.1 q.2)
      (Set.Ici 0 ×ˢ Set.Ioi 0) := by sorry

end MinEarnings.Threshold
