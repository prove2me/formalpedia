-- Prove2me | Theorems.Thm_MasulloGRH_isRapidDecay_elemSchwartz_toFun
-- name    : MasulloGRH.isRapidDecay_elemSchwartz_toFun
-- status  : Proved
-- author  : @sflicht
-- created : 2026-11-21T17:04:13.100214+00:00
-- url     : https://prove2.me/theorems/2a108806-b661-42c9-9d9c-1c3ebd3ba4c1
-- title:
--   Every element of the elementary Schwartz–Bruhat space is of rapid decay
-- statement:
--   Let $E=\mathbb R^m\times\mathbb T^n\times\mathbb Z^r\times\prod_{i<s}\mathbb Z/d_i$ and let $\mathcal S(E)$ be the Schwartz–Bruhat space of Definition D.1.3.1, formalized as the complex linear span of the functions of rapid decay. Then the span adds nothing: every $g\in\mathcal S(E)$ is itself smooth of rapid decay, i.e. each lift $g_{a,b}(x,t)=g(x,[t],a,b)$ is $C^\infty$ on $\mathbb R^m\times\mathbb R^n$ and for all $i,j,k$
--   $$\sup_{a,b,x,t}\ |a|^j\,|x|^i\,\big\|D^k g_{a,b}(x,t)\big\|<\infty .$$
--   Proof: the rapid-decay functions are closed under $0$, sums and scalar multiples (derivatives are linear on smooth functions and the bounds add), so they form a submodule containing the generators.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, Appendix D, Definition D.1.3.1

import Definitions.Def_MasulloGRH_SchwartzBruhat

set_option autoImplicit false

namespace MasulloGRH

theorem isRapidDecay_elemSchwartz_toFun {m n r s : ℕ} {d : Fin s → ℕ}
    (g : ElemSchwartz m n r s d) : IsRapidDecay g.toFun := by
  sorry

end MasulloGRH
