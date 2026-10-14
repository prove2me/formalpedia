-- Prove2me | Theorems.Thm_IntMul_HvdH_Japprox_bound
-- name    : IntMul.HvdH.Japprox_bound
-- status  : Proved
-- author  : @xuanji
-- created : 2026-10-12T00:14:06.843619+00:00
-- url     : https://prove2.me/theorems/6430b63e-d7a6-4c13-931e-7d5ea0d494c6
-- title:
--   Neumann-series approximation of $\mathcal J'$ (Lemma 4.12)
-- statement:
--   Let $p,s,t,\alpha$ be integers with $s\ge1$ and $\alpha^2\theta\ge1$, where $\theta=t/s-1$, i.e. $s\le\alpha^2(t-s)$. Let $m$ = `eWidth p α` be the width of Lemma 4.11, and assume $2(10m+12)\le2^p$. Let $U_i\in\mathbb Z[i]$ with $|U_i|\le2^p$, and put $u=2^{-p}U$. Let $w$ be a bounded solution of $(I+\mathcal E)w=u/2$ with $|w_\ell|\le1$, so that $w=\mathcal J'u$. Then the output $Z$ of `Japprox` (see `IntMul_HvdH_JApprox`) satisfies, for every $\ell$,
--   $$\bigl|Z_\ell-2^pw_\ell\bigr|\le n(10m+12)+1,\qquad n=\lceil p/(\alpha^2\theta)\rceil.$$
--
--   This is Lemma 4.12 of Harvey–van der Hoeven, where the bound is $\tfrac34p^2$. The proof uses $\|\mathcal E\|\le2^{-\alpha^2\theta}\le\tfrac12$ (Lemma 4.6). Lemma 4.11 then shows inductively that each $\tilde v^{(j)}$ is within $10m+12$ of $2^p\mathcal E^jv$. The tail $\mathcal E^nw$ is at most $2^{-\alpha^2\theta n}\le2^{-p}$.
-- source:
--   Harvey, van der Hoeven, Integer multiplication in time O(n log n), Annals of Math. 193 (2021), https://hal.science/hal-02070778, Lemma 4.12

import Definitions.Def_IntMul_HvdH_JApprox
import Theorems.Thm_IntMul_HvdH_Eapprox_bound

namespace IntMul.HvdH
theorem Japprox_bound (p s t α : ℕ) (hs : 0 < s) (hx : s ≤ α ^ 2 * (t - s))
    (hpB : 2 * (10 * eWidth p α + 12) ≤ 2 ^ p)
    (U : ℕ → ℤ × ℤ) (hU : ∀ i, ‖((U i).1 : ℂ) + ((U i).2 : ℂ) * Complex.I‖ ≤ 2 ^ p)
    (w : ℕ → ℂ) (hw : ∀ l, ‖w l‖ ≤ 1)
    (hJ : ∀ l, w l + Eexact s t α w l = (((U l).1 : ℂ) + ((U l).2 : ℂ) * Complex.I) / 2 ^ p / 2)
    (l : ℕ) :
    ‖(((Japprox p s t α U l).1 : ℂ) + ((Japprox p s t α U l).2 : ℂ) * Complex.I) - 2 ^ p * w l‖
      ≤ jIter p s t α * (10 * eWidth p α + 12) + 1 := by sorry
end IntMul.HvdH
