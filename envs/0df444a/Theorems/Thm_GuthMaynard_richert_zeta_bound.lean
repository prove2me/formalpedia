-- Prove2me | Theorems.Thm_GuthMaynard_richert_zeta_bound
-- name    : GuthMaynard.richert_zeta_bound
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-05T20:56:54.408626+00:00
-- url     : https://prove2.me/theorems/d669b41e-ec9a-40b5-aeca-4102100081b6
-- title:
--   Richert's bound — |ζ(σ+it)| ≪ |t|^{B(1−σ)^{3/2}} (log|t|)^{2/3} for 1/2 ≤ σ ≤ 1
-- statement:
--   There are constants $A$ and $B$ such that for all real $\sigma \in [1/2, 1]$ and $t$ with $|t| \ge 2$,
--   $$|\zeta(\sigma + it)| \le A\,|t|^{B(1-\sigma)^{3/2}}(\log|t|)^{2/3}.$$
--
--   This is Richert's bound, H.-E. Richert, *Zur Abschätzung der Riemannschen Zetafunktion in der Nähe der Vertikalen σ = 1*, Math. Ann. 169 (1967) 97–101, https://doi.org/10.1007/BF01399533, in the form K. Ford states it as (1.1) of *Vinogradov's integral and bounds for the Riemann zeta function*, Proc. London Math. Soc. 85 (2002) 565–633, https://doi.org/10.1112/S0024611502013655 (arXiv:1910.08209v1, p. 1): “In 1967, Richert [22] used this method to give the bound (1.1) $|\zeta(\sigma + it)| \le A|t|^{B(1-\sigma)^{3/2}}\log^{2/3}|t|$ $(|t| \ge 2, \frac12 \le \sigma \le 1)$ with $B = 100$ and $A$ and unspecified absolute constant.” Ford's Theorem 1 gives explicit values of $A$ and $B$ for $t \ge 3$. Ford, p. 1, calls the bound “the principal tool” behind the Vinogradov–Korobov zero-free region, which Guth–Maynard (arXiv:2405.20552v2, p. 50) use as `GuthMaynard.zeroDensityCount_eq_zero_vinogradov_korobov`.
--
--   **Formalization note.** The constants are existential, as in Richert's theorem; the value $B = 100$ is not part of the statement.
-- source:
--   Ford, K., Vinogradov's integral and bounds for the Riemann zeta function, Proc. London Math. Soc. 85 (2002) 565–633, https://doi.org/10.1112/S0024611502013655 (arXiv:1910.08209v1, whose page numbers are used), p. 1, (1.1), Richert's bound (Richert, Math. Ann. 169 (1967) 97–101, https://doi.org/10.1007/BF01399533), the input of the Vinogradov–Korobov zero-free region used in Guth–Maynard (arXiv:2405.20552v2), p. 50

import Mathlib

namespace GuthMaynard

theorem richert_zeta_bound :
    ∃ A B : ℝ, ∀ σ t : ℝ, 1 / 2 ≤ σ → σ ≤ 1 → 2 ≤ |t| →
      ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤
        A * |t| ^ (B * (1 - σ) ^ (3 / 2 : ℝ)) * Real.log |t| ^ (2 / 3 : ℝ) := by
  sorry

end GuthMaynard
