-- Prove2me | Theorems.Thm_MasulloRH_trace_formula_rational
-- name    : MasulloRH.trace_formula_rational
-- status  : Open
-- author  : @davidloeffler
-- created : 2026-11-20T19:40:31.085467+00:00
-- url     : https://prove2.me/theorems/88a2d604-a244-4f06-80b6-eef794c58e47
-- title:
--   Theorem 12.5.1.1 — Trace Formula (Riemann zeta specialization)
-- statement:
--   ### Theorem 12.5.1.1 — Trace Formula
--
--   **Source:** Alessandro Maria Masullo, *The Music of the Primes*, frozen 20 November 2026 draft, pp.519–520, equations (12.5.1.1)–(12.5.1.3).
--   https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf
--
--   **Full source statement.** Let $F$ be a number field and $\phi\in\mathcal D(C_F)$ a smooth compactly supported test function on its idele class group. Assume $\phi(g)=0$ for every $g\in C_F^1$. For $I=[-\alpha,\alpha]$, the claimed trace identity is
--   $$
--   \begin{aligned}
--   &\sum_{v\text{ real}}\frac12\int_{F_v^\times}'
--    \frac{\phi(g_v)|g_v|_v^{1/2}}{|1-g_v|_v}\,d\mu_v(g_v)
--   +\sum_{v\text{ complex}}\frac1{2\pi}\int_{F_v^\times}'
--    \frac{\phi(g_v)|g_v|_v^{1/2}}{|1-g_v|_v}\,d\mu_v(g_v)\\
--   &\quad+\sum_{v\text{ finite}}\frac{\log q_v}{\mu_v(\mathcal O_{F_v}^{\times})}
--    \int_{F_v^\times}'\frac{\phi(g_v)|g_v|_v^{1/2}}{|1-g_v|_v}\,d\mu_v(g_v)\\
--   &=\mathcal M(\phi)(|\cdot|_F^{1/2})+
--    \mathcal M(\phi)(|\cdot|_F^{-1/2})-
--    \sum_{c,I}N(c)\mathcal M(\phi)(c|\cdot|_F^{-1/2}).
--   \end{aligned}
--   $$
--   Here $q_v$ is the residue-field size, $\mathcal M(\phi)(c)=\int_{C_F}\phi(g)c(g)\,d\mu(g)$, and the last sum is over zeros of the completed Hecke $L$-function on the quasi-character surface whose real parameter lies strictly inside $1/2+I$. $N(c)$ is the full zero multiplicity, without the degree cap appearing in the later Chapter 13 formula. The primes on the integrals denote the source's principal-value convention. The printed theorem leaves $I$ free; its proof specifies the symmetric interval. The formal node below takes $\alpha>0$.
--
--   **Formal node in this RH project: rational field and norm-invariant test functions.** Put $F=\mathbf Q$ and $\phi(g)=\varphi(|g|_{\mathbf Q})$. Use the source's Tamagawa normalization $\mu_1(C_{\mathbf Q}^1)=1$ and $d\mu_\infty(x)=dx/|x|$. Let $\varphi$ be smooth, compactly supported inside $(0,\infty)$, and satisfy $\varphi(1)=0$. Define
--   $$\Phi(s)=\int_0^\infty\varphi(t)t^s\,\frac{dt}{t},\qquad
--   Z_\alpha=\{\rho\in\mathbf C:\zeta(\rho)=0,\ 0<\Re\rho<1,\ |\Re\rho-1/2|<\alpha\}.$$
--   Then the asserted specialization is
--   $$
--   \begin{aligned}
--   &\int_1^\infty(\varphi(t)+\varphi(t^{-1}))\frac{\sqrt t}{t^2-1}\,dt\\
--   &\quad+\sum_{p\text{ prime}}\sum_{n\ge1}
--    \frac{\log p}{p^{n/2}}(\varphi(p^n)+\varphi(p^{-n}))\\
--   &=\Phi(1/2)+\Phi(-1/2)-\sum_{\rho\in Z_\alpha}
--    \operatorname{ord}_\rho(\zeta)\Phi(\rho-1/2).
--   \end{aligned}
--   $$
--   The Lean statement also requires integrability of the real-place integrand and summability of the prime-power and spectral families **as conclusions**, so a divergent totalized sum cannot satisfy the formula by default. The Mellin transform is Mathlib's actual `mellin`; multiplicity is `analyticOrderNatAt riemannZeta`. The spectral sum ranges over all distinct nontrivial zero locations in the strict strip, counted with these multiplicities, at arbitrary height. The interval boundary is excluded. Keeping the restricted zero sum for every positive $\alpha$ is essential; replacing it with the classical sum over all zeros would change the claim.
--
--   **Position in the intended argument.** The trace formula precedes the limiting/analytic-continuation step of §§1.4.2–1.4.5, which is intended to establish the existing logarithmic-derivative milestone. Its proof cites Theorem 10.4.2.8 (spectral trace), equation (11.3.1.4) and Theorem 11.3.2.1 (orbital decomposition/calculation), and Theorem 12.4.1.1 (S-local trace calculation). These are source dependencies to formalize; no reduction proof connecting this node to the logarithmic-derivative milestone has yet been submitted.
--
--   **Status:** open theorem. Only the rational norm-invariant specialization is encoded in Lean here; the full number-field/Hecke-character formula above is source context, not a claim that those definitions have been formalized. This node records Masullo's proposed result and does not verify it.
--
--
--   ### Independent blind read-back
--
--   For every real $\alpha>0$ and every function $\varphi:\mathbb R\to\mathbb C$ that is infinitely differentiable over $\mathbb R$, has compact topological support contained in $(0,\infty)$, and satisfies $\varphi(1)=0$, the theorem asserts all four of the following together: $t\mapsto(\varphi(t)+\varphi(t^{-1}))\sqrt t/(t^2-1)$ is integrable on $(1,\infty)$ with respect to additive Lebesgue measure; the complex family $(\log p)/\sqrt{p^{n+1}}\,(\varphi(p^{n+1})+\varphi(p^{-(n+1)}))$, indexed by every natural prime $p$ and every natural $n\ge0$, is summable; the complex family $m(\rho)\int_0^\infty t^{\rho-3/2}\varphi(t)\,dt$, indexed once by each complex zero $\rho$ of the actual Riemann zeta function with $0<\Re\rho<1$ and $|\Re\rho-\tfrac12|<\alpha$, is summable; and the identity
--   $$\int_1^\infty(\varphi(t)+\varphi(t^{-1}))\frac{\sqrt t}{t^2-1}\,dt+\sum_{p\ {\rm prime},\,n\ge0}\frac{\log p}{\sqrt{p^{n+1}}}(\varphi(p^{n+1})+\varphi(p^{-(n+1)}))=\int_0^\infty t^{-1/2}\varphi(t)\,dt+\int_0^\infty t^{-3/2}\varphi(t)\,dt-\sum_{\rho}m(\rho)\int_0^\infty t^{\rho-3/2}\varphi(t)\,dt$$
--   holds. Every integral uses additive Lebesgue measure and complex powers on positive real inputs. Both summability assertions mean convergence of the net of sums over finite subsets of the full index set, with no prescribed ordering or height cutoff. The multiplicity $m(\rho)$ is the natural-number analytic vanishing order, defined to be zero at points of nonanalyticity or neighborhoodwise vanishing. The two asserted summability conditions remove the nonsummable-case zero convention for those sums; all displayed integrals remain totalized Bochner integrals, defined to be zero if their integrands are not integrable, and the statement explicitly asserts integrability only for the real trace integrand on $(1,\infty)$.
-- source:
--   Alessandro Maria Masullo, The Music of the Primes, 20 November 2026 draft, Theorem 12.5.1.1, pp.519–520; F=Q, norm-invariant specialization. Haar normalizations: Definitions A.3.1.2, A.3.2.1 and A.3.2.2. https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf

import Definitions.Def_MasulloRH_RationalTrace

set_option autoImplicit false

open MeasureTheory Set
open scoped Topology

namespace MasulloRH

/-- Masullo, Theorem 12.5.1.1: rational-field, norm-invariant specialization.
The strip is open and α is arbitrary positive. Convergence is part of the claim. -/
theorem trace_formula_rational (α : ℝ) (hα : 0 < α) (φ : ℝ → ℂ)
    (hφ : IsRationalTraceTest φ) :
    IntegrableOn (realTraceIntegrand φ) (Ioi 1) ∧
    Summable (primePowerTraceTerm φ) ∧
    Summable (zetaTraceTerm φ α) ∧
    (∫ t in Ioi (1 : ℝ), realTraceIntegrand φ t) +
      (∑' i : Nat.Primes × ℕ, primePowerTraceTerm φ i) =
      mellin φ (1 / 2) + mellin φ (-1 / 2) -
        ∑' ρ : ZetaZerosInTraceStrip α, zetaTraceTerm φ α ρ := by sorry

end MasulloRH
