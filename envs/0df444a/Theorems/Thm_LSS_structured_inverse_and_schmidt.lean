-- Prove2me | Theorems.Thm_LSS_structured_inverse_and_schmidt
-- name    : LSS.structured_inverse_and_schmidt
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-28T13:34:59.799088+00:00
-- url     : https://prove2.me/theorems/89ea7dca-5a8f-4725-ba86-114b713b99ee
-- title:
--   Quasi-polynomial $U^{s+1}$ inverse theorem together with the Schmidt property for one class of structured functions
-- statement:
--   Let $s\ge 3$. There is a class of *structured functions* — a predicate $\mathrm{Str}(N,Q,\varphi)$ on $N\in\mathbb N$, $Q\in\mathbb R$, $\varphi:\mathbb Z\to\mathbb R$ — which simultaneously satisfies
--
--   **(Inverse theorem with quasi-polynomial bounds.)** There is $C>0$ such that for every $N$, every $0<\delta\le1/2$ and every $f:\mathbb Z\to[-1,1]$ supported on $\{1,\dots,N\}$ with
--   $$\sum_{x\in[1,N]}\ \sum_{h_1,\dots,h_{s+1}\in(-N,N)}\ \prod_{\omega\in\{0,1\}^{s+1}} f(x+\omega\cdot h)\ \ge\ \delta^{2^{s+1}}N^{s+2},$$
--   there is $\varphi$ with $\mathrm{Str}(N,Q,\varphi)$, $|\varphi|\le Q$ and $\big|\sum_{x=1}^N f(x)\varphi(x)\big|\ge N/Q$, where $Q=\exp\big(C(1+\log(1/\delta))^C\big)$;
--
--   **(Schmidt property.)** There is $C>0$ such that for all $N,T\in\mathbb N$, $Q\ge1$ and $\varphi_1,\dots,\varphi_T$ with $\mathrm{Str}(N,Q,\varphi_i)$, putting $V=\exp\big(C(1+\log((T+2)(Q+2)))^C\big)$, the set $\{1,\dots,N\}$ can be partitioned into $L$ arithmetic progressions with positive common differences such that $L\,N^{1/V}\le 2N$ and $|\varphi_i(x)-\varphi_i(y)|\le V N^{-1/V}$ whenever $x,y$ lie in the same progression.
--
--   Neither property is hard alone (bounded multiples of bounded functions satisfy the first, constants the second); the content is that one class satisfies both. The class of Lipschitz nilsequences $F(g(n)\Gamma)$ of degree $s$, with dimension at most $1+\log Q$ and complexity and Lipschitz constant at most $Q$ (real parts), does: the first property is the quasi-polynomial $U^{s+1}[N]$ inverse theorem of Leng–Sah–Sawhney, the second is their Schmidt-type lemma for nilsequences. Together with the density increment argument this yields $r_k(N)\le N\exp(-(\log\log N)^{c_k})$ for $k\ge5$.
-- source:
--   J. Leng, A. Sah, M. Sawhney, Quasipolynomial bounds for the inverse theorem for the Gowers U^{s+1}[N]-norm, arXiv:2402.17994, Theorem 1.2; and J. Leng, A. Sah, M. Sawhney, Improved bounds for Szemerédi's theorem, arXiv:2402.17995, Section 2 (Schmidt-type lemma for nilsequences; the inverse theorem is quoted there in Section 3)

import Mathlib
import Definitions.Def_LSSInterface

namespace LSS

theorem structured_inverse_and_schmidt (s : ℕ) (hs : 3 ≤ s) :
    ∃ Str : ℕ → ℝ → (ℤ → ℝ) → Prop, InvHyp Str s ∧ SchmidtHyp Str := by sorry

end LSS
