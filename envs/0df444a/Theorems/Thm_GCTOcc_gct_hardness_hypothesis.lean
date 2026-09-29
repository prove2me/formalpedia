-- Prove2me | Theorems.Thm_GCTOcc_gct_hardness_hypothesis
-- name    : GCTOcc.gct_hardness_hypothesis
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-14T18:03:32.861855+00:00
-- url     : https://prove2.me/theorems/246e2069-28fe-4f54-bb26-eb1d049ece67
-- title:
--   The GCT hardness hypothesis: $\mathrm{per}_n$ is not approximable by symbolic determinants of size $2^{n^{\varepsilon}}$
-- statement:
--   There is a constant $\varepsilon > 0$ such that, for all sufficiently large $n$, the permanent $\mathrm{per}_n$ cannot be approximated infinitesimally closely by symbolic determinants of size $s \le 2^{n^{\varepsilon}}$; in the orbit-closure formulation,
--
--   $$X_{00}^{\,s-n}\,\mathrm{per}_n \;\notin\; \Omega_s \qquad \text{for all } n \le s \le 2^{n^{\varepsilon}} .$$
--
--   This hypothesis, an algebraic-geometric strengthening of $\mathbf{VP}\ne\mathbf{VNP}$, is the hardness assumption under which Noether normalization for explicit varieties is brought from $\mathbf{EXPSPACE}$ down to quasi-polynomial time in GCT V. It is open. It is stated here in the same vocabulary as the rest of the mission, since "approximated infinitesimally closely by symbolic determinants of size $s$" is exactly membership of the padded permanent in the orbit closure $\Omega_s$ of $\det_s$, that is, border determinantal complexity larger than $s$.
--
--   **Formalization note.** The asymptotic $O(2^{n^{\varepsilon}})$ is rendered without a separate constant: a constant factor in the bound can be absorbed by decreasing $\varepsilon$, so the statement quantifies over sizes $s$ with $(s:\mathbb{R}) \le 2^{n^{\varepsilon}}$ and $s \ge n$. The base field is $\mathbb{C}$.
-- source:
--   K. D. Mulmuley, *Geometric Complexity Theory V: Efficient algorithms for Noether normalization*, J. Amer. Math. Soc., https://doi.org/10.1090/jams/864, p. 4, Introduction §1.2: the hardness hypothesis for the permanent in geometric complexity theory — 'the permanent of $n\times n$ matrices cannot be approximated infinitesimally closely by symbolic determinants over $K$ of $O(2^{n^{\epsilon}})$ size, for some constant $\epsilon>0$, as $n\to\infty$'; used in Theorem 5.11(b) and §5.5.

import Definitions.Def_GCTOcc_occurrence
open MvPolynomial

namespace GCTOcc

theorem gct_hardness_hypothesis :
    ∃ ε : ℝ, 0 < ε ∧ ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ∀ s : ℕ, n ≤ s →
      (s : ℝ) ≤ 2 ^ ((n : ℝ) ^ ε) → paddedPerm n s ∉ orbitClosure s (detPoly s) := by sorry

end GCTOcc
