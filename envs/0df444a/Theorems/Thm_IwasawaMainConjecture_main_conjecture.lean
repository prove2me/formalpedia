-- Prove2me | Theorems.Thm_IwasawaMainConjecture_main_conjecture
-- name    : IwasawaMainConjecture.main_conjecture
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-12T17:25:55.211886+00:00
-- url     : https://prove2.me/theorems/e5707147-e08f-4f34-8637-8c5d40535897
-- title:
--   Main conjecture of Iwasawa theory (Mazur–Wiles)
-- statement:
--   Let $p$ be a prime, $F_n = \mathbb{Q}(\mu_{p^{n+1}})$, $H_\infty = \varprojlim A_n$ the inverse limit of the $p$-parts of the class groups of $F_n$ under the norm maps, $V = H_\infty \otimes_{\mathbb{Z}_p} \mathbb{Q}_p$, and $V_i$ the $\omega^i$-eigenspace of $V$, where $\omega$ is the Teichmüller character. Let $\gamma \in \mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ and $u \in \mathbb{Z}_p^\times$ satisfy $\gamma(\zeta) = \zeta^u$ for every $p$-power root of unity $\zeta$, and suppose $u$ topologically generates $1 + p\mathbb{Z}_p$ (so $\gamma$ restricts to a topological generator of $\Gamma = \mathrm{Gal}(F_\infty/F_0)$). Let
--   $$h_p(\omega^i, T) = \det\big(T - (\gamma - 1) \mid V_i\big)$$
--   be the characteristic polynomial of $\gamma$ on $V_i$ in the Iwasawa variable $T = \gamma - 1$.
--
--   **Theorem (Mazur–Wiles).** If $i$ is an odd integer with $i \not\equiv 1 \pmod{p-1}$, then there is a power series $G_p(\omega^{1-i}, T) \in \mathbb{Z}_p[[T]]$ with
--   $$G_p(\omega^{1-i}, u^{1-k} - 1) = L_p(\omega^{1-i}, 1-k) = -\frac{B_{k,\omega^{1-i-k}}}{k} \qquad (k \ge 1).$$
--   Moreover $h_p(\omega^i, T)$ has coefficients in $\mathbb{Z}_p$, and
--   $$\big(h_p(\omega^i, T)\big) = \big(G_p(\omega^{1-i}, T)\big)$$
--   as ideals of $\mathbb{Z}_p[[T]]$.
--
--   This identifies the characteristic polynomial of the Iwasawa module with the $p$-adic $L$-function. The Herbrand–Ribet theorem and the Gras conjecture are consequences.
--
--   **Formalization Note** The power series $G_p$ is stated existentially, and a power series with this interpolation property is unique. $h_p \in \mathbb{Q}_p[T]$ is compared with $G_p$ through its (unique) preimage in $\mathbb{Z}_p[T]$. Because $h_p$ is defined to be $0$ if $V_i$ were infinite-dimensional, the statement also asserts that $V_i$ is finite-dimensional. The source describes $h_p$ as "the characteristic polynomial of $\gamma$ acting on $V_i$"; for the stated ideal equality to hold, the polynomial must be read in the variable $T = \gamma - 1$ of $\mathbb{Z}_p[[T]] \cong \mathbb{Z}_p[[\Gamma]]$, i.e. as $\det(T - (\gamma - 1))$. Taken literally, $\det(T - \gamma)$ has a unit constant term and would generate the unit ideal.
-- source:
--   Wikipedia, "Main conjecture of Iwasawa theory", revision oldid=1367440598, https://en.wikipedia.org/w/index.php?title=Main_conjecture_of_Iwasawa_theory&oldid=1367440598, section "Statement", final paragraph; Mazur–Wiles, Class fields of abelian extensions of Q, Invent. Math. 76 (1984), https://doi.org/10.1007/BF01388599

import Definitions.Def_IwasawaMainConjecture_algebraic
import Definitions.Def_IwasawaMainConjecture_analytic

open scoped Polynomial

namespace IwasawaMainConjecture
theorem main_conjecture (p : ℕ) [Fact p.Prime] (i : ℤ) (hi_odd : Odd i)
    (hi : ¬ i ≡ 1 [ZMOD ((p : ℤ) - 1)])
    (γ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (u : ℤ_[p]ˣ)
    (hγ : IsCyclotomicCharValue p γ u) (hu : IsTopologicalGenerator p u) :
    ∃ G : PowerSeries ℤ_[p], IsIwasawaPowerSeries p u (1 - i) G ∧
      ∃ h : ℤ_[p][X], h.map (algebraMap ℤ_[p] ℚ_[p]) = charPoly p i γ ∧
        Ideal.span {(h : PowerSeries ℤ_[p])} = Ideal.span {G} := by sorry
end IwasawaMainConjecture
