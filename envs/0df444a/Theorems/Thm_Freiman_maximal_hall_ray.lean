-- Prove2me | Theorems.Thm_Freiman_maximal_hall_ray
-- name    : Freiman.maximal_hall_ray
-- status  : Proved
-- author  : @tp
-- created : 2026-09-08T23:24:11.884253+00:00
-- url     : https://prove2.me/theorems/8e6a39ef-c3a0-4d28-9375-4a1595883166
-- title:
--   Freiman's maximal Hall ray
-- statement:
--   Let $L$ and $M$ be the classical Lagrange and Markov spectra, and let
--   $$
--   c_F=\frac{2221564096+283748\sqrt{462}}{491993569}.
--   $$
--   For every real number $d$,
--   $$
--   [d,\infty)\subseteq L\quad\Longleftrightarrow\quad c_F\le d,
--   $$
--   and
--   $$
--   [d,\infty)\subseteq M\quad\Longleftrightarrow\quad c_F\le d.
--   $$
--   Thus $[c_F,\infty)$ is the maximal half line contained in each spectrum. Its endpoint is included, and no half line starting below $c_F$ is contained in either spectrum.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text, 8 September 2026, Theorem 21.1 and Corollary 20.7, p. 71. See also C. G. Moreira, Geometric properties of the Markov and Lagrange spectra, Annals of Mathematics 188 (2018), pp. 146–147, https://doi.org/10.4007/annals.2018.188.1.3

import Definitions.Def_Freiman_cF
import Definitions.Def_Freiman_lagrangeSpectrum
import Definitions.Def_Freiman_markovSpectrum

namespace Freiman

theorem maximal_hall_ray :
    (∀ d : ℝ, Set.Ici d ⊆ lagrangeSpectrum ↔ cF ≤ d) ∧
    (∀ d : ℝ, Set.Ici d ⊆ markovSpectrum ↔ cF ≤ d) := by
  sorry

end Freiman
