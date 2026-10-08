-- Prove2me | Theorems.Thm_MethanolMuDrift_rotational_sensitivity_eq_neg_one
-- name    : MethanolMuDrift.rotational_sensitivity_eq_neg_one
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-04T21:19:03.939061+00:00
-- url     : https://prove2.me/theorems/f253c9b5-4266-459c-8e08-67578801b963
-- title:
--   Pure rotational transitions have $K_\mu=-1$
-- statement:
--   Let $C\neq 0$ be a constant and let a transition frequency depend on the proton-to-electron mass ratio $\mu$ as
--   $$\nu(\mu)=\frac{C}{\mu},$$
--   i.e. it is inversely proportional to $\mu$, as is the case for pure rotational transitions (whose frequency is inversely proportional to the reduced mass of the molecule). Then at every $\mu>0$ its sensitivity coefficient $K_\mu=\frac{\mu}{\nu}\frac{d\nu}{d\mu}$ equals
--   $$K_\mu=-1 .$$
--   This is the value used for the two $0_0$–$1_0$ lines ($A^+$ and $E$) in Table 1 and serves as the reference point against which the enhanced sensitivities of mixed torsion–rotation transitions are compared.
--
--   **Formalization Note** The sensitivity coefficient is the logarithmic derivative $(\mu/\nu(\mu))\,\nu'(\mu)$ from the definition file; the model "frequency proportional to $1/\mu$" is taken as the hypothesis, exactly as stated in the paper.
-- source:
--   J. Bagdonaite, P. Jansen, C. Henkel, H. L. Bethlem, K. M. Menten, W. Ubachs, "A Stringent Limit on a Drifting Proton-to-Electron Mass Ratio from Alcohol in the Early Universe", Science (First Release, 13 December 2012), doi:10.1126/science.1224898, https://doi.org/10.1126/science.1224898, p. 1 (right column): definition $\Delta\nu/\nu=K_\mu\,\Delta\mu/\mu$ and "the frequency of pure rotational transitions ... are inversely proportional to the reduced mass of methanol and hence to the proton-to-electron mass ratio. Consequently, these have sensitivity coefficients equal to -1."

import Mathlib
import Definitions.Def_Bagdonaite2013_MethanolMuDrift

namespace MethanolMuDrift

theorem rotational_sensitivity_eq_neg_one (C μ : ℝ) (hC : C ≠ 0) (hμ : 0 < μ) :
    sensitivityCoeff (fun m => C / m) μ = -1 := by sorry

end MethanolMuDrift
