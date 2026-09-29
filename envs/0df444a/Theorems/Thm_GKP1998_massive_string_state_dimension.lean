-- Prove2me | Theorems.Thm_GKP1998_massive_string_state_dimension
-- name    : GKP1998.massive_string_state_dimension
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-26T00:55:28.624288+00:00
-- url     : https://prove2.me/theorems/798eb276-2794-41c8-ab0c-4e16d6524254
-- title:
--   GKP 1998, Eqs. (41)–(46): two-point function and dimension of operators dual to massive string states
-- statement:
--   Let $n\ge1$ be an integer and $N,g_{YM},\alpha',m,R>0$ with $m^2=4n/\alpha'$ and $R^4=2Ng_{YM}^2\alpha'^2$, and suppose $\nu=\sqrt{4+(mR)^2}$ is not an integer. Then:
--
--   1. (Eq. (44)) there is a function $A$, real-analytic at $0$, with
--   $$\frac{N^2}{16\pi^2}\mathcal F_\nu(k)=A(k^2)-\frac{N^2}{8\pi^2}\frac{\Gamma(1-\nu)}{\Gamma(\nu)}\Big(\frac{kR}{2}\Big)^{2\nu}R^{-4}+o\big(k^{2\nu}\big)\qquad(k\to0^+);$$
--   2. (Eqs. (41), (45)) $\Delta=2+\nu=2+\sqrt{4+4n\,g_{YM}\sqrt{2N}}$;
--   3. (Eq. (46)) $\dfrac{2+\sqrt{4+4n\,g\sqrt{2N}}}{2\sqrt{n\,g\sqrt{2N}}}\to1$ as $g\to+\infty$.
--
--   Here $\mathcal F_\nu(k)=[z^{-3}\partial_z\log\tilde f_k(z)]_{z=R}$ with $\tilde f_k(z)=z^2K_\nu(kz)/(R^2K_\nu(kR))$, so that $\langle O(k)O(q)\rangle=(2\pi)^4\delta^4(k+q)\frac{N^2}{16\pi^2}\mathcal F_\nu(k)$ (Eq. (26)). The non-integrality assumption is implicit in the source, where $\Gamma(1-\nu)$ appears.
-- source:
--   S.S. Gubser, I.R. Klebanov, A.M. Polyakov, Gauge theory correlators from non-critical string theory, Phys. Lett. B 428 (1998) 105-114, arXiv:hep-th/9802109, pp. 110-113, Eqs. (26), (41)-(46)

import Definitions.Def_GKP1998_Defs

open Filter Topology Asymptotics

namespace GKP1998
/-- Goal (Eqs. (41)–(46)): for a scalar string state at level `n ≥ 1` with `m² = 4n/α'`,
`R⁴ = 2 N g_YM² α'²` and non-integer Bessel order `ν = √(4 + (mR)²)`:
(i) the two-point function of the dual operator is an analytic function of `k²` plus the
leading non-analytic term `−N²/(8π²) · Γ(1−ν)/Γ(ν) · (kR/2)^{2ν} · R⁻⁴` (Eq. (44)), up to
`o(k^{2ν})` as `k → 0⁺`;
(ii) the dimension of the dual operator is `Δ = 2 + ν = 2 + √(4 + 4 n g_YM √(2N))`
(Eqs. (41), (45));
(iii) for fixed `n ≥ 1` and `N > 0`, `Δ ∼ 2 (n g_YM √(2N))^{1/2}` as `g_YM → ∞` (Eq. (46)). -/
theorem massive_string_state_dimension (n : ℕ) (hn : 1 ≤ n) (N gYM α' m R : ℝ)
    (hN : 0 < N) (hg : 0 < gYM) (hα : 0 < α') (hm : 0 < m) (hR : 0 < R)
    (hmass : m ^ 2 = 4 * n / α') (hradius : R ^ 4 = 2 * N * gYM ^ 2 * α' ^ 2)
    (hνZ : ∀ j : ℤ, massiveOrder m R ≠ j) :
    (∃ A : ℝ → ℝ, AnalyticAt ℝ A 0 ∧
      (fun k : ℝ => twoPointFunction N (massiveOrder m R) k R - A (k ^ 2)
          - (-(N ^ 2 / (8 * Real.pi ^ 2)) * Real.Gamma (1 - massiveOrder m R)
              / Real.Gamma (massiveOrder m R) * (k * R / 2) ^ (2 * massiveOrder m R) / R ^ 4))
        =o[𝓝[>] (0 : ℝ)] (fun k : ℝ => k ^ (2 * massiveOrder m R))) ∧
    scalingDimension (massiveOrder m R) = 2 + Real.sqrt (4 + 4 * n * gYM * Real.sqrt (2 * N)) ∧
    Tendsto (fun g : ℝ =>
        scalingDimension (Real.sqrt (4 + 4 * n * g * Real.sqrt (2 * N)))
          / (2 * Real.sqrt (n * g * Real.sqrt (2 * N))))
      atTop (𝓝 1) := by sorry
end GKP1998
