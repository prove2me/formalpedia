-- Prove2me | Theorems.Thm_MFHeisGibbs_eq_25_29
-- name    : MFHeisGibbs.eq_25_29
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:57:49.663344+00:00
-- url     : https://prove2.me/theorems/4f3151ca-0c04-41a4-9f7b-3051d3f15084
-- title:
--   (25), with the variance orders behind (29) — the phase diagram of $\mathcal L_{DM}$
-- statement:
--   For every $0\le\beta<\infty$,
--
--   $$\gamma(\mathcal L_{DM})=\begin{cases}\Theta(1),&\beta<2,\\\Theta(n^{-1/2}),&\beta=2,\\\Theta(n^{-1}),&\beta>2.\end{cases}$$
--
--   Moreover $\mathrm{Tr}(\rho M_z)=0$ for $M_z=S^z_{\mathrm{tot}}$, and there is $c>0$ with $\mathrm{Var}_\rho(M_z)\ge cn$ for $\beta<2$ and with $\mathrm{Var}_\rho(M_z)\ge cn^2$ for $\beta>2$, for all $n\ge2$.
--
--   This is the input from which all three generators inherit the diagram. The off-critical part is a result of Basso et al. and the critical part is new in the source.
--
--   Differences from the source:
--   - encoding: (25), which the page proves by citing [BBL+26, Theorem 1.1] for β ≠ 2, and the variance bounds cited to [BBL+26, Lemma 3.23] → posed here as a target and not assumed; reason: the statement is unchanged; neither weaker nor stronger than the page. Being proved in the mission, it adds no assumption
--   - encoding: O(·) in (29) → explicit lower bounds on Var_ρ(M_z) with one constant for all n ≥ 2; reason: each variance is positive, so a bound for large n extends to all n ≥ 2
--   - encoding: Θ(·) → ∃ c, C > 0 after β, for all n ≥ 2, with a scalar kernel; reason: p.41 fixes Θ as n → ∞ with β fixed; each gap is positive so the bounds extend to all n ≥ 2
-- source:
--   Raikovich, Mák, Czabán, Gilyén, arXiv:2610.06818 (version dated November 3, 2026, sha256 164d57ba…), (25), p.8 (PDF 9); (26), (29), p.9 (PDF 10)

import Definitions.Def_MFHeisGibbs_Generators
import Definitions.Def_MFHeisGibbs_Gap
import Definitions.Def_MFHeisGibbs_KMS

open Matrix

namespace MFHeisGibbs

/-- **(25), with the variance orders behind (29) and (26)**, Raikovich, Mák, Czabán, Gilyén, arXiv:2610.06818 (version dated November 3, 2026, sha256 164d57ba…),
pp.8–9. For every `0 ≤ β < ∞`, `γ(L_DM) = Θ(1)` for `β < 2`, `Θ(n^{−1/2})` at `β = 2`, `Θ(n^{−1})` for
`β > 2`, with `Tr(ρM_z) = 0`, `Var_ρ(M_z) ≥ cn` for `β < 2` and `Var_ρ(M_z) ≥ cn²` for `β > 2`.

**Formalization Note.** The paper takes the off-critical part from [BBL+26, Theorem 1.1, Lemma 3.23]; here
it is posed as a milestone, not assumed. `M_z = S^z_tot` is `Stot n 2`. -/
theorem eq_25_29 :
    (∀ β : ℝ, 0 ≤ β → GapOrder (LDM β) (phase β)) ∧
    (∀ (β : ℝ) (n : ℕ), 0 ≤ β → 2 ≤ n → trace (rhoPow β 1 n * Stot n 2) = 0) ∧
    (∀ β : ℝ, 0 ≤ β → β < 2 → ∃ c > 0, ∀ n : ℕ, 2 ≤ n →
      c * (n : ℝ) ≤ gibbsVar β (Stot n 2)) ∧
    (∀ β : ℝ, 2 < β → ∃ c > 0, ∀ n : ℕ, 2 ≤ n →
      c * (n : ℝ) ^ 2 ≤ gibbsVar β (Stot n 2)) := by sorry

end MFHeisGibbs
