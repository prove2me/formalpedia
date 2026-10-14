-- Prove2me | Theorems.Thm_IwasawaMainConjecture_finiteDimensional_V
-- name    : IwasawaMainConjecture.finiteDimensional_V
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-12T17:23:58.393953+00:00
-- url     : https://prove2.me/theorems/9a0d782f-4e41-49b0-ad42-4022530cb5e7
-- title:
--   $V = H_\infty\otimes_{\mathbb{Z}_p}\mathbb{Q}_p$ is finite-dimensional
-- statement:
--   Let $p$ be a prime, $F_n = \mathbb{Q}(\mu_{p^{n+1}})$, $A_n$ the $p$-part of the class group of $F_n$, and $H_\infty = \varprojlim_n A_n$ the inverse limit under the norm maps. Then
--   $$V = H_\infty \otimes_{\mathbb{Z}_p} \mathbb{Q}_p$$
--   is a finite-dimensional $\mathbb{Q}_p$-vector space.
--
--   This follows from Iwasawa's theorem that $H_\infty$ is a finitely generated torsion module over $\Lambda = \mathbb{Z}_p[[\Gamma]]$; $\dim_{\mathbb{Q}_p} V$ is Iwasawa's $\lambda$-invariant. Finite-dimensionality is what makes "the characteristic polynomial of $\gamma$ acting on $V_i$" in the source meaningful.
-- source:
--   Wikipedia, "Main conjecture of Iwasawa theory", revision oldid=1367440598, https://en.wikipedia.org/w/index.php?title=Main_conjecture_of_Iwasawa_theory&oldid=1367440598, section "Statement" (h_p(ω^i,T) is the characteristic polynomial of γ acting on the vector space V_i); Iwasawa, On some modules in the theory of cyclotomic fields, J. Math. Soc. Japan 16 (1964), https://doi.org/10.2969/jmsj/01610042

import Definitions.Def_IwasawaMainConjecture_algebraic
import Definitions.Def_IwasawaMainConjecture_analytic

open scoped Polynomial

namespace IwasawaMainConjecture
theorem finiteDimensional_V (p : ℕ) [Fact p.Prime] : FiniteDimensional ℚ_[p] (V p) := by sorry
end IwasawaMainConjecture
