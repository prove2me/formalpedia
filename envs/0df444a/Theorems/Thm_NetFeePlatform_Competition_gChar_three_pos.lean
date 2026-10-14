-- Prove2me | Theorems.Thm_NetFeePlatform_Competition_gChar_three_pos
-- name    : NetFeePlatform.Competition.gChar_three_pos
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T08:31:48.234417+00:00
-- url     : https://prove2.me/theorems/2816a757-4029-460e-a47e-9386fb6e96bb
-- title:
--   Proof of Proposition 4, p. 50 — for 2 ln 2 + 4/3 < γ ≤ 27/8, g(n; 3) > 0 at every zero n ∈ (0, 1/2] of g(·; 2)
-- statement:
--   Let $\gamma$ satisfy
--   $$2\ln2+\frac43<\gamma\le\frac{27}{8}.$$
--   If $0<n\le\frac12$ is a zero of the duopoly characterization function, $g(n;2)=0$, then
--   $$g(n;3)>0.$$
--
--   Here $n\le1/2$ is the share of the smaller platform of a duopoly equilibrium (with $n=1/2$ the symmetric equilibrium, which is a zero of $g(\cdot;2)$ for every $\gamma$). Combined with $\lim_{n\to0^+}g(n;3)=-\infty$, it yields a triopoly equilibrium whose two small platforms have total share below $n$.
--
--   **Formalization Note** The paper writes the condition as $f(n,3)<f(n,2)$ with $f(n,J)$ the solution of $g(n;J)=0$ for $\gamma$, and asserts it for $\gamma\in(2.71,3.375]$ after a numerical check. Since $g(n;J)=2\big(\tfrac{n}{J-1}-(1-n)\big)\big(f(n,J)-\gamma\big)$ and the first factor is negative for $n<\tfrac{J-1}{J}$, the two forms agree wherever $f$ is defined; but $f(\cdot,2)$ is $0/0$ at $n=1/2$, so the $f$-form omits the symmetric duopoly equilibrium. At $n=1/2$ the condition reads $-\ln2+\tfrac43-2+\tfrac\gamma2>0$, i.e. $\gamma>2\ln2+\tfrac43\approx2.7196$, which is why the lower end of the paper's range $2.71$ is replaced by $2\ln2+\tfrac43$.
-- source:
--   Ekmekci, White & Wu, Platform Competition and Interoperability: The Net Fee Model, accepted working-paper version (December 12, 2024), p. 50, Appendix E.2, proof of Proposition 4

import Mathlib
import Definitions.Def_NetFeePlatform_Competition_Setting
import Definitions.Def_NetFeePlatform_Competition_GChar

namespace NetFeePlatform.Competition
theorem gChar_three_pos (γ : ℝ) (hlo : 2 * Real.log 2 + 4 / 3 < γ) (hhi : γ ≤ 27 / 8) :
    ∀ n : ℝ, 0 < n → n ≤ 1 / 2 → gChar γ 2 n = 0 → 0 < gChar γ 3 n := by sorry
end NetFeePlatform.Competition
